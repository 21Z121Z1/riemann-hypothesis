import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlacesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  first | exact @GlobalTheory.Nef.exists_frame_locFrames | exact GlobalTheory.Nef.exists_frame_locFrames | (intros; apply GlobalTheory.Nef.exists_frame_locFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.FlatCM.GramExists

theorem exists_weilEq_entry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → p + q = 1 →
    HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ →
    Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hpq hA f₁ f₂ h₁ h₂
  obtain ⟨A', B', f₁', f₂', p', q', hpq', hdet, h₁', h₂', hW⟩ := GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple E H K ρ σ₁ A B p q hρ hA f₁ f₂ h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type E H A' B' p' q' (hpq'.trans hpq) hdet f₁' f₂' h₁' h₂'
  exact ⟨g, hW g hg⟩

theorem exists_isGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X
  have hP : ∀ a b : Fin p, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L
      ((X.A true).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP _ _ (X.lin (Sum.inl a)) (X.lin (Sum.inl b))
  have hQ : ∀ a b : Fin q, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L
      ((X.A false).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A false) X.B 0 1 X.ρ_sq rfl X.typeM _ _ (X.lin (Sum.inr a)) (X.lin (Sum.inr b))
  choose gP hgP using hP
  choose gQ hgQ using hQ
  exact ⟨Matrix.of gP, Matrix.of gQ, fun a b => hgP a b, fun a b => hgQ a b⟩

end GlobalTheory.FlatCM.GramExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestrictionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_character_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 1 := by
  first | exact @GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one | exact GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one | (intros; apply GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroup
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypPairSelfDual

theorem exists_partner : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  intro D S Λ x hΛ hx0 hxx
  set σ : D.host.E →ₐ[D.host.F] D.host.E := D.sp.cm.sig with hσdef
  have hσs : ∀ e : D.host.E, σ e = star e := fun _ => rfl
  have hσ : ∀ e, σ (σ e) = e := fun e => by rw [hσs, hσs, star_star]
  set J : Matrix (Fin S.rank) (Fin S.rank) D.host.E := Matrix.transpose (HSpace.gram S) with hJ
  set co : S.V ≃ₗ[D.host.E] (Fin S.rank → D.host.E) := S.frame.equivFun with hco

  have hform : ∀ a b : S.V, S.hT a b = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co b) (co a) := fun a b => by
    rw [GlobalTheory.RelFlag.hT_eq_form]
    simp only [GlobalTheory.SgAlg.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IntPair.co, dotProduct, Matrix.mulVec, hJ,
      Matrix.transpose_apply, hσs, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hco]; ring
  have hframe : ∀ i, co (S.frame i) = Pi.single i 1 := fun i => by
    ext j; simp [hco, Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hherm : ∀ i j, σ (J j i) = J i j := fun i j => by
    have h1 := S.herm.eq (S.frame i) (S.frame j)
    have e1 : S.hT (S.frame i) (S.frame j) = J j i := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    have e2 : S.hT (S.frame j) (S.frame i) = J i j := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e1, e2] at h1
    rw [hσs]; simpa [starRingEnd_apply] using h1
  have hfg : Λ.FG := hΛ.1.fg
  have hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v) := fun w => by
    rw [hΛ.2 w]
    refine forall₂_congr fun v _ => ?_
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v = ∑ i, ∑ j, star (v i) * S.gram i j * w j := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, hJ, Matrix.transpose_apply, hσs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← GlobalTheory.PlaneSplit.mem_range_iff]
    simp [RingHom.mem_range, eq_comm]
  have hfu : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := GlobalTheory.HeckeAdjoint.unramified_host D; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E σ
    (GlobalTheory.AdelicU.isCMExt_host D) hfu
  have hcx0 : co x ≠ 0 := fun h => hx0 (co.injective (by rw [h, map_zero]))
  have hcxx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co x) (co x) = 0 := by rw [← hform]; exact hxx
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing D.host.F D.host.E σ hσ S.rank J Λ hfg hherm hdual (co x) hcx0
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module D.host.F D.host.E σ S.rank J Λ hfg (co x) ⟨z0, hz0L, hz0⟩
  obtain ⟨y, hyy, hxy, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice D.host.F D.host.E σ hσ S.rank J Λ hherm hdual θ hθ (co x) y₀ hcxx hy₀1 hy₀L
  have hconj : ∀ a b, σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun a b => by
    have hh' : ∀ i j, σ (J i j) = J j i := fun i j => hherm j i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hh']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨co.symm y, ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hform, co.apply_symm_apply]; exact hyy
  · rw [hform, co.apply_symm_apply, ← hconj, hxy, map_one]
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform, co.apply_symm_apply]
    exact (hL _ hz).1
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform]
    change _ • co (co.symm y) ∈ Λ
    rw [co.apply_symm_apply]
    exact (hL _ hz).2

end GlobalTheory.HypPairSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  first | exact @GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | exact GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | (intros; apply GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 → Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  first | exact @GlobalTheory.BottomIsom.isoMat_of_posDef | exact GlobalTheory.BottomIsom.isoMat_of_posDef | (intros; apply GlobalTheory.BottomIsom.isoMat_of_posDef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCurvePhaseEqOfClose
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PhaseMove

theorem trace_sum_int : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → ∃ m : ℤ, 2 * (∑ τ, Formalism.MainNotions.TaylorLogMetric.embT D τ w).re = m := by
  intro D w hw
  have htr := Formalism.MainNotions.Ext.trace_sum_over_letters_holds D w
  have ht : IsIntegral ℤ (Algebra.trace D.host.K D.host.E w) := Algebra.isIntegral_trace hw
  obtain ⟨u, v, huv⟩ := ((GlobalTheory.MomDict.main D).2.2.1 _).2 ⟨⟨_, ht⟩, rfl⟩
  refine ⟨2 * u + v, ?_⟩
  rw [htr]
  erw [huv]
  simp [GlobalTheory.MomOne.wK]
  ring

def cTA (D : D7) {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin p) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  (B.map (Formalism.MainNotions.StandardLatticesGL3.sgA D)).transpose

theorem sq_unitary : ∀ {D : D7} {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∑ i, ∑ j, (((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j)) = ∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j) := by
  intro D a d x y A
  have hinv : ∀ e : D.host.E, D.host.conj (D.host.conj e) = e := fun e => by
    apply D.host.φ₀.injective
    have h1 := D.host.conjE_apply D.host.φ₀
    change D.host.φ₀ (D.host.conj (D.host.conj e)) = _
    rw [h1, h1, Complex.conj_conj]
  have hsg : ∀ u : Formalism.MainNotions.StandardLatticesGL3.AE D, Formalism.MainNotions.StandardLatticesGL3.sgA D (Formalism.MainNotions.StandardLatticesGL3.sgA D u) = u := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul e r =>
      change (Algebra.TensorProduct.map _ _) ((Algebra.TensorProduct.map _ _) (e ⊗ₜ r)) = e ⊗ₜ r
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact hinv e
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hΦ : ∀ B : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∑ i, ∑ j, B i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (B i j)) = (B * cTA D B).trace := fun B => by
    simp [cTA, Matrix.trace, Matrix.mul_apply]
  have hmul : ∀ {m p q : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (C : Matrix (Fin p) (Fin q) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (B * C) = cTA D C * cTA D B := fun B C => by
    simp only [cTA, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : ∀ {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (cTA D B) = B := fun B => by
    ext i j; simp [cTA, hsg]
  have hU : ∀ {m : ℕ} (g : Formalism.MainNotions.StandardLatticesGL3.GA D m), cTA D ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := fun g => by
    have h := g.2
    change Formalism.UG.cT _ _ * ((1 : Matrix _ _ D.host.E).map _) * _ = (1 : Matrix _ _ D.host.E).map _ at h
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    exact h
  set X : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hX
  set V : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hV
  set Y : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hY
  have hVX : V * X = 1 := by rw [hV, hX, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXc : X * cTA D X = 1 := mul_eq_one_comm.1 (hU x)
  have hVe : V = cTA D X := by
    calc V = V * (X * cTA D X) := by rw [hXc, Matrix.mul_one]
      _ = cTA D X := by rw [← Matrix.mul_assoc, hVX, Matrix.one_mul]
  have hVV : V * cTA D V = 1 := by rw [hVe, hcc, hU x]
  rw [hΦ, hΦ, hmul, hmul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hY1 : cTA D Y * Y = 1 := hU y
  rw [Matrix.mul_assoc (cTA D A), hY1, Matrix.mul_one, Matrix.trace_mul_comm]

theorem sq_move_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ A' : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∀ i j, ∃ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, A' i j - A i j = (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) → ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, (∑ i, ∑ j, A' i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A' i j)) - (∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j)) = (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  intro D cc a d A M hM
  obtain ⟨B, hB, hBA⟩ := GlobalTheory.NormSum.Expand.denom_fin (fun k : Fin d × Fin a => A k.1 k.2)
  obtain ⟨m, hm, hmI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D cc
  refine ⟨M * B * m, by positivity, fun A' hA' => ?_⟩
  choose t ht et using hA'
  have hsg : ∀ u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, Formalism.MainNotions.StandardLatticesGL3.sgA D u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun u hu =>
    GlobalTheory.NormSum.UnramHecke.sgA_mem D hu
  have hA1 : ∀ i j, (B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hBA (i, j)
  have ht1 : ∀ i j, (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hmI _ (ht i j)
  refine ⟨∑ i, ∑ j, (((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) +
      ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) +
      ((M * B * B : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j))),
    sum_mem fun i _ => sum_mem fun j _ => add_mem (add_mem (mul_mem (hA1 i j) (hsg _ (ht1 i j)))
      (mul_mem (ht1 i j) (hsg _ (hA1 i j)))) (mul_mem (natCast_mem _ _) (mul_mem (ht1 i j) (hsg _ (ht1 i j)))), ?_⟩
  have hA' : ∀ i j, A' i j = A i j + ((M * B * m : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j := fun i j => by
    rw [← et i j]; ring
  simp only [hA', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_mul, map_natCast]
  push_cast
  ring

theorem sq_diff_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ z' : Matrix (Fin d) (Fin a) D.host.E, Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' → IsIntegral ℤ (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) := by
  intro D cc a d x y z M hM
  obtain ⟨n, hn, h⟩ := sq_move_int cc ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)))) M hM
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨s, hs, e⟩ := h (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) fun i j => by
    obtain ⟨t, ht, et⟩ := hz' i j
    exact ⟨t, ht, by rw [← et, Matrix.sub_apply]⟩
  rw [sq_unitary] at e
  have hinc : ∀ w : Matrix (Fin d) (Fin a) D.host.E, (∑ i, ∑ j, w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j)) = Formalism.MainNotions.StandardLatticesGL3.inc D (∑ i, ∑ j, w i j * D.host.conj (w i j)) := fun w => by
    simp only [Matrix.map_apply, map_sum, map_mul]
    rfl
  rw [hinc, hinc, ← map_sub] at e
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← GlobalTheory.HeckeVal.inc_mem_iff]
  have e2 : Formalism.MainNotions.StandardLatticesGL3.inc D (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) = Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    rw [div_eq_inv_mul, map_mul, e, mul_assoc]
  have e3 : Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
    rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hM0, map_one]
  rw [e2, e3, one_mul]
  exact hs

theorem qH_pt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.qH D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) =
      (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))).re / (Ideal.absNorm cc : ℝ) := by
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hC
  have hN : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  have hd : (0 : ℝ) < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hc : ∀ τ x, embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) := fun τ x =>
    D.host.conjE_apply (embT D τ) x
  have hpt : ∀ τ i j, pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := fun τ i j => rfl
  have hS : ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j)) =
      ∑ τ, ∑ i, ∑ j, embT D τ (z i j) * starRingEnd ℂ (embT D τ (z i j)) := by
    simp only [map_sum, map_mul, hc]
  have hH : Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ z) =
      ((Complex.normSq δ : ℝ) : ℂ) * (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))) /
        ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [hS, Hf]
    simp only [hpt, map_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [Formalism.MainNotions.TaylorLogMetric.qH, hH, GlobalTheory.MomDict.area_lamOf D cc δ hC.1.1]
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  rw [show ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) =
    ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) from rfl,
    mul_div_assoc, Complex.re_ofReal_mul, Complex.div_ofReal_re]
  field_simp

theorem phase_eq : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D cc δ hC a d x y z
  have hN : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  obtain ⟨n, hn, h⟩ := sq_diff_int cc x y z (8 * Ideal.absNorm cc) (by positivity)
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨m, hm⟩ := trace_sum_int D _ (h z' hz')
  set S' := ∑ i, ∑ j, z' i j * D.host.conj (z' i j)
  set S := ∑ i, ∑ j, z i j * D.host.conj (z i j)
  have h8 : ((8 * Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hsplit : S' = S + ((8 * Ideal.absNorm cc : ℕ) : D.host.E) * ((S' - S) / ((8 * Ideal.absNorm cc : ℕ) : D.host.E)) := by
    field_simp; ring
  have key : (∑ τ, embT D τ S').re = (∑ τ, embT D τ S).re + 4 * (Ideal.absNorm cc : ℝ) * m := by
    rw [hsplit]
    simp only [map_add, map_mul, map_natCast, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re]
    have e : ((8 * Ideal.absNorm cc : ℕ) : ℂ) = (((8 * Ideal.absNorm cc : ℕ) : ℝ) : ℂ) := rfl
    rw [e, Complex.re_ofReal_mul]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hN' : (0 : ℝ) < Ideal.absNorm cc := by exact_mod_cast hN
  have harg : (∑ τ, embT D τ S').re / (Ideal.absNorm cc : ℝ) / 2 =
      (∑ τ, embT D τ S).re / (Ideal.absNorm cc : ℝ) / 2 + 2 * m := by
    rw [key]; field_simp; ring
  rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.StandardLatticesGL3.wdPh, qH_pt hC z', qH_pt hC z, harg]
  unfold Formalism.MainNotions.StandardLatticesGL3.ee
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2 * m, ?_⟩
  push_cast
  ring

end GlobalTheory.PhaseMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdealStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.MaxLevelLift.exists_intG_cong | exact GlobalTheory.MaxLevelLift.exists_intG_cong | (intros; apply GlobalTheory.MaxLevelLift.exists_intG_cong <;> assumption)
end

