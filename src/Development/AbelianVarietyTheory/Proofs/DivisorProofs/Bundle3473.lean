import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3456
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularForm
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMaximalIdealOfTrdegLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace GlobalTheory

theorem eq_maximalIdeal_of_trdeg_le (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra F A] (hA : Algebra.EssFiniteType F A) (p : Ideal A)
    (hp : p.IsPrime)
    (htr : Algebra.trdeg F (FractionRing (A ⧸ p)) ≤ Algebra.trdeg F (ResidueField A)) :
    p = maximalIdeal A := by
  classical
  by_contra hne
  have hle : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  obtain ⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  haveI := hA
  haveI : Algebra.EssFiniteType F (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A))
      (IsLocalRing.residue_surjective)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField A)
  haveI : Finite s := finite_of_isTranscendenceBasis hs
  let f : A ⧸ p →ₐ[F] ResidueField A :=
    Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by
      simpa [IsLocalRing.residue_eq_zero_iff] using hle hx)
  have hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x := fun x => rfl
  choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1
  let z : s → A ⧸ p := fun i => Ideal.Quotient.mk p (y i)
  have hfz : f ∘ z = ((↑) : s → ResidueField A) := by
    funext i
    simp only [Function.comp_apply, z, hfmk, hy]
  have hz : AlgebraicIndependent F z := by
    have h1 := hs.1
    rw [← hfz] at h1
    exact h1.of_comp f
  set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef
  have hb0 : b ≠ 0 := by
    rw [hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hap
  have hbk : b ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk p a) = 0
    rw [hfmk, IsLocalRing.residue_eq_zero_iff]
    exact ham
  have hinj := algebraicIndependent_iff_injective_aeval.mp hs.1
  have htrans : Transcendental (Algebra.adjoin F (Set.range z)) b := by
    intro halg
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker] at hc
    have hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R := F) z).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨g, hg⟩ := hc2
    have h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0 := by
      rw [← hfz]
      change MvPolynomial.aeval (fun i => f (z i)) g = 0
      rw [← MvPolynomial.comp_aeval_apply]
      change f ((MvPolynomial.aeval z).toRingHom g) = 0
      rw [hg]
      exact hc
    have hg0 : g = 0 := hinj (by rw [h0, map_zero])
    rw [Ideal.mem_bot]
    apply Subtype.ext
    rw [← hg, hg0, map_zero]
    rfl
  have hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z) :=
    AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩
  have hopt' := hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p)))
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))
  have hc1 := hopt'.cardinalMk_le_trdeg
  rw [← hs.cardinalMk_eq_trdeg] at htr
  have hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s := hc1.trans htr
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hle2
  haveI := Fintype.ofFinite s
  have := Fintype.card_le_of_embedding e
  rw [Fintype.card_option] at this
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.proj_unique (h : IsOpp D Z Z') {a b b' : D.La} (hb : b ∈ Z') (hb' : b' ∈ Z')
    (h1 : a - b ∈ perp D Z) (h2 : a - b' ∈ perp D Z) : b = b' := by
  have := h.eq_zero (sub_mem hb hb') (by
    have := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at this)
  exact sub_eq_zero.1 this

def IsOpp.proj (h : IsOpp D Z Z') : D.La →ₗ[𝓞 E] Z' where
  toFun a := ⟨(h.exists_sub_mem_perp a).choose, (h.exists_sub_mem_perp a).choose_spec.1⟩
  map_add' a b := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hb := (h.exists_sub_mem_perp b).choose_spec
    have hab := (h.exists_sub_mem_perp (a + b)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hab.1 (add_mem ha.1 hb.1) hab.2 ?_
    have := add_mem ha.2 hb.2
    simpa [sub_add_sub_comm] using this
  map_smul' c a := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hca := (h.exists_sub_mem_perp (c • a)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hca.1 (Z'.smul_mem c ha.1) hca.2 ?_
    have := (perp D Z).smul_mem c ha.2
    simpa [smul_sub] using this

theorem IsOpp.sub_proj_mem (h : IsOpp D Z Z') (a : D.La) : a - h.proj a ∈ perp D Z :=
  (h.exists_sub_mem_perp a).choose_spec.2

theorem IsOpp.proj_eq (h : IsOpp D Z Z') {a b : D.La} (hb : b ∈ Z') (hab : a - b ∈ perp D Z) : (h.proj a : D.La) = b :=
  h.proj_unique (h.proj a).2 hb (h.sub_proj_mem a) hab

theorem IsOpp.proj_of_mem (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') : (h.proj b : D.La) = b :=
  h.proj_eq hb (by simp)

theorem IsOpp.proj_of_perp (h : IsOpp D Z Z') {a : D.La} (ha : a ∈ perp D Z) : (h.proj a : D.La) = 0 :=
  h.proj_eq Z'.zero_mem (by simpa using ha)

variable (D)

theorem exists_adjoint (σ : D.La →ₗ[𝓞 E] D.La) : ∃ w : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (w a) b = D.EF a (σ b) := by
  choose w hw using fun a => D.unimod.2 ((D.EF a).comp (σ.restrictScalars ℤ))
  refine ⟨{ toFun := w, map_add' := fun a b => D.unimod.1 ?_, map_smul' := fun c a => D.unimod.1 ?_ }, fun a b => ?_⟩
  · ext x; simp [hw]
  · ext x
    simp only [hw, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, RingHom.id_apply, D.adj]
    rw [← σ.map_smul]
  · exact congrArg (fun f => f b) (hw a)

theorem bijective_of_isometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) :
    Function.Bijective g := by
  obtain ⟨w, hw⟩ := exists_adjoint D g
  have hwg : ∀ a, w (g a) = a := fun a => D.unimod.1 (LinearMap.ext fun b => by rw [hw, hg])
  have hws : Function.Surjective w := fun a => ⟨g a, hwg a⟩
  haveI := D.fin
  have hwi : Function.Injective w := OrzechProperty.injective_of_surjective_endomorphism w hws
  refine ⟨fun a b hab => by rw [← hwg a, ← hwg b, hab], fun a => ⟨w a, hwi (by rw [hwg])⟩⟩

def equivOfIsometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) : D.La ≃ₗ[𝓞 E] D.La :=
  LinearEquiv.ofBijective g (bijective_of_isometry D g hg)

@[simp] theorem equivOfIsometry_apply (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) (a : D.La) :
    equivOfIsometry D g hg a = g a := rfl

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosurStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  first | (exact @GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (exact GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (intros; apply GlobalTheory.EtC.hInv_tensorPower_integralClosure  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartFunctionOfWeightUnitLogDerivStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianPart_function_of_weight_unit_logDeriv : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (α : Q.X) (U : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ U ≤ h.W i → ∀ x : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U), IsUnit x → IsWt Y α _ x → ∃ A : Γ(Q.P.A.left, U), (Y.q.left.app U).hom A * x = dE h ν i _ x := by
  first | exact @GlobalTheory.HeatConn.LogDerDesc.exists_app_mul_eq_dE | exact GlobalTheory.HeatConn.LogDerDesc.exists_app_mul_eq_dE | (intros; apply GlobalTheory.HeatConn.LogDerDesc.exists_app_mul_eq_dE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatMod.TorUniq
open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)
open GlobalTheory.HeatMod.TorField

theorem exists_addHom_of_kills_wt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd e he
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  have hc : IsLieComb e u (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) := (GlobalTheory.SqZero.isLieComb_iff_lieExp e _).2 rfl
  have ht := GlobalTheory.Reg.isTangent_of_isLieComb hb.1 hc
  have hq : GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q = 1 :=
    Over.OverMorphism.ext (GlobalTheory.T.spec_hom_ext_of_localization_at_primes _ _ _ _ fun P _ => GlobalTheory.T.tangent_killing_weight_zero_maps_to_abelianPart_unit R Q O oa Y n (fun a => v a) u hb.1 hu dd hd e he _ _)
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_torus_tangent_of_raynaud_tangent_over_unit R Q O oa Y _ ht hq
  refine ⟨ℓ, fun α V f hf => ?_⟩
  show combF Y.H.hom dd e _ f = _
  refine sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := GlobalTheory.SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => GlobalTheory.SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g _ hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (e i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) _ a₁ Finset.univ
  have E0 := congrArg (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ ·) hℓ.symm
  simp only [GlobalTheory.SqZero.comp_lieExp, ← Category.assoc] at E0
  rw [GlobalTheory.SqZero.lieExp] at E0
  rw [← E0] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left (Y.q.left ⁻¹ᵁ V) s = inl (valR g _ s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add]; rfl
  simp only [a₃, hψ, hu'] at k'
  rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg, combF,
    GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

end GlobalTheory.HeatMod.TorUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatHullLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.UPoinc.ChartAt

theorem isUnit_map_of_ne_zero {o R : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [CommRing R]
    (hR : ∀ n : ℤ, n ≠ 0 → IsUnit (n : R)) (φ : o →+* R) {a : o} (ha : a ≠ 0) : IsUnit (φ a) := by
  by_contra h
  obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
  letI := Ideal.Quotient.field m
  haveI : CharZero (R ⧸ m) := charZero_of_inj_zero fun n hn => by
    by_contra h0
    have hu := (hR n (by exact_mod_cast h0)).map (Ideal.Quotient.mk m)
    exact hu.ne_zero (by simpa using hn)
  have hk := ker_eq_bot_of_charZero ((Ideal.Quotient.mk m).comp φ)
  have : a ∈ RingHom.ker ((Ideal.Quotient.mk m).comp φ) := Ideal.Quotient.eq_zero_iff_mem.2 ham
  rw [hk] at this
  exact ha this

theorem exists_affine_chart_ratHull_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w₀ ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw _ l Xo cf C X w hw
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  haveI := C.isPreimmersion_i
  haveI : CharZero X.Ω₁ := by
    obtain ⟨t, -⟩ := Spec.map_surjective (X.uΩ ≫ pullback.snd _ _)
    exact (RingHom.charZero_iff (R := cf.F) t.hom.injective).1 inferInstance
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨V, hV, hVe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ X.π ⁻¹ᵁ ⟨V, hV⟩ := by
    obtain ⟨x, hx⟩ := hw
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' V := hVe ▸ ⟨x, rfl⟩
    show X.π w ∈ V
    rw [← hx]
    exact this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of (ratHull (X.M.ringOn U)) :=
    CommRingCat.ofHom ((toRat (X.M.ringOn U)).comp (X.M.sectionsEquiv U hne).toRingHom)
  let f : Sp (ratHull (X.M.ringOn U)) ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (f ≫ X.π ≫ C.z)
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (ψ.hom a) := fun a =>
    isUnit_map_of_ne_zero (fun n hn => isUnit_intCast_ratHull _ hn) ψ.hom (nonZeroDivisors.ne_zero a.2)
  let χ : cf.F →+* ratHull (X.M.ringOn U) := IsLocalization.lift (M := nonZeroDivisors C.o) hu
  have hχ : (f ≫ X.π) ≫ C.z = spMap χ ≫ spMap C.b := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun t => spMap t) (IsLocalization.lift_comp (M := nonZeroDivisors C.o) hu).symm
  let g := pullback.lift _ _ hχ
  have hgf : g ≫ pullback.fst _ _ = f ≫ X.π := pullback.lift_fst _ _ _
  have hrange : Set.range g ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hVe]
    show (g ≫ pullback.fst C.z (spMap C.b)) y ∈ V
    rw [hgf]
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact hUV this
  refine ⟨U, IsOpenImmersion.lift C.iF g hrange, hU, hwU, ?_⟩
  rw [← cancel_mono C.i, Category.assoc, Category.assoc, ← X.comp, UCompact.i, IsOpenImmersion.lift_fac_assoc, hgf]
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (ratHull (X.M.ringOn U)).val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [Category.assoc]

end GlobalTheory.UPoinc.ChartAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisPullbackMatrixInvariantFieldsRaynaud
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.InvFactor

section Lie
variable {R : Type} [CommRing R] {G B : Over (Sp R)} [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B]

theorem smT_comp (a : R) (v : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G) (φ : G ⟶ B) :
    smT (𝟙 (Sp R)) a (v ≫ φ) = smT (𝟙 (Sp R)) a v ≫ φ := (Category.assoc _ _ _).symm

def lieMap (q : G ⟶ B) [IsMonHom q] : TanM (𝟙 (Sp R)) G →ₗ[R] TanM (𝟙 (Sp R)) B where
  toFun v := ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (tv v ≫ q) (by rw [smT_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.one_comp])
  map_add' u v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (MonObj.mul_comp (tv u) (tv v) q)
  map_smul' a v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (smT_comp a (tv v) q).symm

theorem tv_lieMap (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) : tv (lieMap q v) = tv v ≫ q := rfl

end Lie

theorem exists_basis_pull_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R) (Qm : Matrix (Fin n) (Fin g) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) ∧ P * Qm = 1 ∧ ∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd
  have hB : Smooth Dd.toPre.P.A.hom := Dd.toPre.P.isAb.smooth
  obtain ⟨g, ⟨w⟩⟩ := GlobalTheory.RayBasis.exists_basis hB
  choose e he using fun c => GlobalTheory.RayBasis.exists_isInv (w c)
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  have hq : Smooth Y.q.left := Y.smooth_q
  let L := lieMap Y.q
  choose s hs using fun c => GlobalTheory.T.smooth_commGroupSchemeHom_tangentAtOrigin_surjective R Y.H Dd.toPre.P.A Y.q hq (w c)
  have hs' : ∀ c, L (s c) = w c := fun c => ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (hs c)
  refine ⟨g, w, e, Matrix.of fun c b => w.repr (L (v b)) c, Matrix.of fun b c => v.repr (s c) b, he, ?_, ?_⟩
  · ext c c'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have h1 : w.repr (L (s c')) c = ∑ b, w.repr (L (v b)) c * v.repr (s c') b := by
      conv_lhs => rw [← v.sum_repr (s c')]
      rw [map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    rw [← h1, hs', w.repr_self, Matrix.one_apply, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro b V W hW f
    have hu : ∑ c, Matrix.of (fun c b => w.repr (L (v b)) c) c b • w c = L (v b) := w.sum_repr _
    have hinv := GlobalTheory.T.invariant_vectorField_of_tangent_vector_linear_combination R Dd.toPre.P.A g w e he (fun c => Matrix.of (fun c b => w.repr (L (v b)) c) c b)
    rw [hu] at hinv
    rw [GlobalTheory.T.invariant_vectorField_pullback_along_group_hom R Y.H Dd.toPre.P.A Y.q (v b) (L (v b)) (dd b) _ rfl (hdd b) hinv V W hW f, GlobalTheory.KS.pbT_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_constFn _ _ hW, Over.w Y.q, Matrix.of_apply]

end GlobalTheory.InvFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) →
  ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
  ∃ (D' : DegData R (maximalIdeal R)) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) ∧
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) ∧ w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tensPol | exact GlobalTheory.Mum.TensPol.exists_tensPol | (intros; apply GlobalTheory.Mum.TensPol.exists_tensPol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_heat_connection_on_abelian_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  first | exact @GlobalTheory.HeatConn.exists_connK_desc | exact GlobalTheory.HeatConn.exists_connK_desc | (intros; apply GlobalTheory.HeatConn.exists_connK_desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualOneFormsInvariantFieldsAffineOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.GcDual.exists_dual_forms | exact GlobalTheory.GcDual.exists_dual_forms | (intros; apply GlobalTheory.GcDual.exists_dual_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatumStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gradedTateIso_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  first | exact @GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | exact GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | (intros; apply GlobalTheory.LowDat.GradedTate.exists_gradedTateIso <;> assumption)
end
end

