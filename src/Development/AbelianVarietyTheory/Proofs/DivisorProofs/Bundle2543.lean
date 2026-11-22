import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem secMaps_secPull_of_pointwise : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LL.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ) (LM.pull fst)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k) →
    ∀ (th : LP.Sec) (σ : LL.Sec) (σ' : LM.Sec),
      (∀ (j : (LL.pull φ).ι) (i : LP.ι) (h : (LL.pull φ).U j ⊓ LP.U i ≤ φ ⁻¹ᵁ LL.U (j PUnit.unit)),
        (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
          (show Γ(XA, (LL.pull φ).U j ⊓ LP.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (th.f i)) →
      GlobalTheory.Cartier.SecMaps e σ' σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull th θ) (GlobalTheory.Cartier.secPull σ' fst) := by
  intro Y XA XG θ φ fst hfst LP LL LM hLL ψ e w₀ hw th σ σ' hth he
  subst hfst
  rintro ⟨J, K⟩
  apply fn_ext
  intro y hy
  have hj : (θ ≫ φ) y ∈ LM.U (J PUnit.unit) := mem_pull.1 hy.1
  have hk : θ y ∈ LP.U (K PUnit.unit) := mem_pull.1 hy.2
  obtain ⟨i, hi⟩ := exists_chart hLL ((θ ≫ φ) y)
  have hm1 : (θ ≫ φ) y ∈ LL.U i ⊓ LM.U (J PUnit.unit) := ⟨hi, hj⟩
  have hm2 : θ y ∈ (LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit) := ⟨mem_pull.2 hi, hk⟩
  have ha := congrArg (gs (θ ≫ φ) y (LL.U i ⊓ LM.U (J PUnit.unit))) (he (i, J PUnit.unit))
  have hb := congrArg (gs θ y ((LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit)))
    (hth (fun _ => i) (K PUnit.unit) (inf_le_left.trans fun x hx => mem_pull.1 hx))
  have hc := hw Y (𝟙 Y) y i (J PUnit.unit) (K PUnit.unit) hi hj hk
  simp only [Category.id_comp] at hc
  rw [gs_mul _ y _ hm1, gs_unit _ y _ hm1] at ha
  change gs _ y _ (resG XG _ _) = _ * gs _ y _ (resG XG _ _) at ha
  rw [gs_res _ y _ hm1, gs_res _ y _ hm1] at ha
  dsimp only at hb
  erw [gs_mul _ y _ hm2, gs_unit _ y _ hm2] at hb
  change _ = _ * gs _ y _ (resG XA _ _) at hb
  rw [gs_res _ y _ hm2] at hb
  have hb' : gs (θ ≫ φ) y (LL.U i) (σ.f i) =
      (gw ψ θ y i (K PUnit.unit)).val * gs θ y (LP.U (K PUnit.unit)) (th.f (K PUnit.unit)) :=
    (gs_pull θ φ y _ hi _).symm.trans ((gs_res θ y _ hm2 _).symm.trans hb)
  have hm3 : (𝟙 Y) y ∈ (LM.pull (θ ≫ φ)).U J := hy.1
  have hm4 : (𝟙 Y) y ∈ (LP.pull θ).U K := hy.2
  change gs (𝟙 Y) y _ (resG Y _ (resG Y _ _)) = _
  erw [gs_res _ y _ hy, gs_res _ y _ hm3, gs_pull (𝟙 Y) (θ ≫ φ) y _ hj, gs_mul _ y _ hy, gs_unit _ y _ hy]
  change _ = _ * gs (𝟙 Y) y _ (resG Y _ (resG Y _ _))
  erw [gs_res _ y _ hy, gs_res _ y _ hm4, gs_pull (𝟙 Y) θ y (LP.U (K PUnit.unit)) hk]
  simp only [Category.id_comp]
  change _ = (gw w₀ (𝟙 Y) y (J PUnit.unit) fun _ => K PUnit.unit).val * _
  rw [hc, Units.val_mul, _root_.mul_assoc, ← hb']
  dsimp only [id] at ha
  rw [ha, Units.inv_mul_cancel_left]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven.ThetaNorm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  intro V _ _ _ _ hc D A G _ _ hG U σ σ₁ f hNz hch hE C _ _ _ _ _ _ hC N ν hI ϑ c hϑ hV
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL4 : Laws4 := GlobalTheory.allSixLaws.2.2.2.1
  have hS : SecBaseChangeSt := hL.secBaseChange
  have h1 : ReciprocityTheory.ChartRestriction.G.DVR.NonzeroOnSpecial U σ₁ := by
    obtain ⟨z, hz, hzn⟩ := hNz (IsLocalRing.closedPoint V)
    refine GlobalTheory.ThetaUnit.nonzeroOnSpecial_of_mem U σ₁ z hz ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hzn
    have hle : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i :=
      fun y hy => Set.mem_iInter.1 hy 0
    have hzi : z ∈ U.LG.L.U i := G.left.basicOpen_le _ hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
    rw [hch i hle]
    change z ∈ G.left.basicOpen ((G.left.presheaf.map (homOfLE hle).op) (σ.f i))
    rw [Scheme.basicOpen_res]
    exact ⟨fun _ ⟨k, hk⟩ => hk ▸ hzi, hi⟩
  have hCL : CLND V := (GlobalTheory.ThetaCompare.clnd_iff_of_dvr V).2 hc
  obtain ⟨f', hf', hgen'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.isTheta_of_nonzeroOnSpecial' hL hL4 hCL rfl U σ₁ h1 0
  have hgen := GlobalTheory.ThetaCompare.secBGenerates_of_expandsAt hS le_rfl U.toUnifPre hf' (hE 0) hgen'
  obtain ⟨g, hg⟩ := GlobalTheory.ThetaCompare.exists_corr_right D.toPre ν.th
  have hgg := (GlobalTheory.ThetaCompare.generates_iff_secBGenerates hS hg).1 (fun s => ν.th_gen s)
  have hgs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul (g : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgg
  have hfs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul ((f 0 : D.toPre.SecB 1 0) : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgen
  obtain ⟨u, hu⟩ := (GlobalTheory.ThetaCompare.generates_iff_unit_smul (fun s => (hgs s).exists) _).1 (fun s => (hfs s).exists)
  have hum : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D.toPre.P.A.hom (u : V) (f 0) g :=
    (GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 hu

  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := GlobalTheory.Ex.FamVal.good ν z
  have hcst : ∀ a : C, cst (𝟙 (Sp C)) z a = toStk z a := fun a => by
    rw [cst, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ _ ⊤ trivial, toStk]
    rfl
  have hc0 : N.c 0 = 1 := by
    have h := N.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hx : ∀ x, c * N.th x * ν.rg = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) * (N.th x * ν.rg) := by
    intro x
    have H := (GlobalTheory.Ex.FamVal.famV_iff ν z ϑ _).1 hV 0 x
    have e1 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal (hϑ 0) (GlobalTheory.Ex.FamVal.pt ν x).left z hJ
    have e2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul hum
      ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e3 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal hg ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e4 : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
      (congrArg (toStk z) (ν.th_eq x)).trans (GlobalTheory.Ex.FamVal.toStk_sF hJ _ _)
    have ep : (GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left = (ν.eA x).left := by
      rw [← Over.comp_left, lift_snd]
    rw [map_zero] at H
    rw [Category.comp_id, ep, ← e4] at e3
    rw [ep] at e2
    rw [e1, ep, e2, ← e3] at H
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, pow_one] at H
    have ec : cst ((ν.eA x).left ≫ D.toPre.P.A.hom) z (u : V) =
        toStk z (algebraMap (FractionRing V) C (algebraMap V _ (u : V))) := by
      have ew : (ν.eA x).left ≫ D.toPre.P.A.hom =
          (𝟙 (Sp C) ≫ spMap (algebraMap (FractionRing V) C)) ≫ spMap (algebraMap V (FractionRing V)) := by
        rw [Category.id_comp]; exact Over.w (ν.eA x)
      rw [ew, cst_comp, cst_comp, hcst]
    have ev : N.vth 0 x = N.th x := by
      simp [NumD.vth, N.ψ_zero, hc0]
    rw [ev, ← GlobalTheory.Ex.FamVal.rg_eq, ec, ← map_mul, ← map_mul] at H
    exact (toStk z).injective H
  have hL2 : Laws2 := GlobalTheory.abelianSchemeLaws_all.2
  have hB := GlobalTheory.Ex.brFam hL hL2 V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨x, hx0⟩ : ∃ x, N.th x ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨s, f0, hf0, hne⟩ := hB.2.2.2.1
    obtain ⟨c', hc'⟩ := hB.2.2.2.2.1 s f0 hf0
    refine hne ?_
    rw [hc']
    funext α y
    simp [NumD.vth, hno]
  have hcu : c = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) := by
    have h := hx x
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel₀ (mul_ne_zero hx0 (GlobalTheory.Ex.FamVal.rg_ne ν)) h
  have n1 := hC.1 (u : V)
  have n2 := hC.1 ((u⁻¹ : Vˣ) : V)
  have hprod : ‖algebraMap (FractionRing V) C (algebraMap V _ (u : V))‖ *
      ‖algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  rw [hcu]
  nlinarith [norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))),
    norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ (u : V)))]

end GlobalTheory.KeyEven.ThetaNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem isPushout_app_of_isPullback {X X₁ T T₁ : Scheme.{0}} {f : X₁ ⟶ X} {p₁ : X₁ ⟶ T₁} {p : X ⟶ T}
    {j : T₁ ⟶ T} (h : IsPullback f p₁ p j) [IsAffine T] [IsAffine T₁] {W : X.Opens}
    (hW : IsAffineOpen W) :
    IsAffineOpen (f ⁻¹ᵁ W) ∧
      IsPushout (p.appLE ⊤ W le_top) j.appTop (f.app W) (p₁.appLE ⊤ (f ⁻¹ᵁ W) le_top) := by
  have : IsAffine W.toScheme := hW
  have sq : IsPullback (f ∣_ W) ((f ⁻¹ᵁ W).ι ≫ p₁) (W.ι ≫ p) j :=
    (isPullback_morphismRestrict f W).paste_vert h
  have : IsAffine (f ⁻¹ᵁ W).toScheme := IsAffine.of_isPullback sq
  refine ⟨this, ?_⟩
  exact (ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip inferInstance (isAffineOpen_top T) hW le_top le_top).flip

theorem appLE_congr_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ a ⁻¹ᵁ U) (h' : V ≤ b ⁻¹ᵁ U) : a.appLE U V h = b.appLE U V h' := by
  subst e; rfl

theorem isPullback_app_of_affine {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W))
    (hV : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V) :
    IsPullback (f₁.app W) (f₂.app W) (g₁.appLE _ V hV₁) (g₂.appLE _ V hV₂) := by
  have := hM.aff; have := hM.aff₁; have := hM.aff₂; have := hM.closed
  obtain ⟨hT₀, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine k₂
  obtain ⟨hU₁, P₁⟩ := isPushout_app_of_isPullback h₁ hW
  obtain ⟨hU₂, P₂⟩ := isPushout_app_of_isPullback h₂ hW
  obtain ⟨-, P₀⟩ := isPushout_app_of_isPullback h₀ hU₂
  have hVe : V = g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := by
    refine le_antisymm hV₂ ?_
    have : g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
    exact this.le.trans hV
  subst hVe
  have e₂ : g₂.appLE (f₂ ⁻¹ᵁ W) (g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) hV₂ = g₂.app (f₂ ⁻¹ᵁ W) :=
    Scheme.Hom.appLE_eq_app ..
  rw [e₂]
  have hfl : (p.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  refine GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective _ _ _ _ _ _ _ _ j₁.appTop j₂.appTop k₁.appTop k₂.appTop hM.cart hsurj _ _ _ _ _ _ _ _
    hfl P₁ P₂ P₀ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_eq hg _ _ _ _
  · have : k₁.appTop = k₁.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app ..).symm
    rw [this]
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    exact appLE_congr_eq hp _ _ _ _

theorem app_restrict_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U W : Y.Opens} (h : U ≤ W) (a : Γ(Y, W)) :
    f.app U (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem appLE_restrict_eq {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (h : V ≤ g ⁻¹ᵁ U) (h' : V' ≤ g ⁻¹ᵁ U') (a : Γ(Y, U)) :
    g.appLE U' V' h' (Y.presheaf.map (homOfLE hU).op a) =
      X.presheaf.map (homOfLE hV).op (g.appLE U V h a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem elem_of_isPullback_ring {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {i : C ⟶ D} (H : IsPullback f g h i) :
    (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ b c, h b = i c → ∃ a, f a = b ∧ g a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem sections_of_squares {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] (W : X.Opens) :
    (∀ a b : Γ(X, W), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b) ∧
    ∀ (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)),
      g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)),
        g₁.appLE _ V hV₁ a₁ = g₂.appLE _ V hV₂ a₂ →
          ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂ := by
  have hpre : ∀ U : X.Opens, g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ U) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) := fun U ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
  have aff : ∀ U : X.Opens, IsAffineOpen U → IsPullback (f₁.app U) (f₂.app U)
      (g₁.appLE _ (g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U)) le_rfl) (g₂.appLE _ _ (hpre U).ge) :=
    fun U hU ↦ isPullback_app_of_affine hM h₁ h₂ h₀ hg hp hU _ le_rfl (hpre U).ge le_rfl
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), f₁.app U a = f₁.app U b →
      f₂.app U a = f₂.app U b → a = b := by
    intro U a b ha hb
    refine TopCat.Presheaf.section_ext X.sheaf U a b fun x hx ↦ ?_
    change X.presheaf.germ U x hx a = X.presheaf.germ U x hx b
    obtain ⟨U', hU', hxU', hle⟩ := exists_isAffineOpen_mem_and_subset hx
    have hle' : U' ≤ U := hle
    rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxU' a,
      ← X.presheaf.germ_res_apply (homOfLE hle') x hxU' b]
    congr 1
    refine (elem_of_isPullback_ring (aff U' hU')).1 _ _ ?_ ?_
    · rw [app_restrict_eq, app_restrict_eq, ha]
    · rw [app_restrict_eq, app_restrict_eq, hb]
  refine ⟨inj W, ?_⟩
  intro V hV₁ hV₂ hV a₁ a₂ he
  have loc : ∀ x : W, ∃ U : X.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧ ∃ hUW : U ≤ W, ∃ c : Γ(X, U),
      f₁.app U c = X₁.presheaf.map (homOfLE (f₁.preimage_mono hUW)).op a₁ ∧
      f₂.app U c = X₂.presheaf.map (homOfLE (f₂.preimage_mono hUW)).op a₂ := by
    intro x
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset x.2
    have hUW : U ≤ W := hle
    refine ⟨U, hU, hxU, hUW, (elem_of_isPullback_ring (aff U hU)).2 _ _ ?_⟩
    have hVU : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) ≤ V := (g₁.preimage_mono (f₁.preimage_mono hUW)).trans hV
    rw [appLE_restrict_eq g₁ (f₁.preimage_mono hUW) hVU hV₁,
      appLE_restrict_eq g₂ (f₂.preimage_mono hUW) hVU hV₂, he]
  choose U hU hxU hUW c hc₁ hc₂ using loc
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro x y
    change X.presheaf.map (homOfLE (inf_le_left : U x ⊓ U y ≤ U x)).op (c x) =
      X.presheaf.map (homOfLE (inf_le_right : U x ⊓ U y ≤ U y)).op (c y)
    apply inj
    · rw [app_restrict_eq, app_restrict_eq, hc₁, hc₁, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [app_restrict_eq, app_restrict_eq, hc₂, hc₂, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' U W (fun x ↦ homOfLE (hUW x))
    (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩) c compat
  have ha' : ∀ x, X.presheaf.map (homOfLE (hUW x)).op a = c x := ha
  refine ⟨a, ?_, ?_⟩
  · refine TopCat.Presheaf.section_ext X₁.sheaf _ _ _ fun y hy ↦ ?_
    change X₁.presheaf.germ _ y hy _ = X₁.presheaf.germ _ y hy _
    have hyU : y ∈ f₁ ⁻¹ᵁ U ⟨f₁ y, hy⟩ := hxU ⟨f₁ y, hy⟩
    rw [← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU,
      ← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU a₁,
      ← app_restrict_eq f₁ (hUW ⟨f₁ y, hy⟩) a, ha' ⟨f₁ y, hy⟩, hc₁]
  · refine TopCat.Presheaf.section_ext X₂.sheaf _ _ _ fun y hy ↦ ?_
    change X₂.presheaf.germ _ y hy _ = X₂.presheaf.germ _ y hy _
    have hyU : y ∈ f₂ ⁻¹ᵁ U ⟨f₂ y, hy⟩ := hxU ⟨f₂ y, hy⟩
    rw [← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU,
      ← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU a₂,
      ← app_restrict_eq f₂ (hUW ⟨f₂ y, hy⟩) a, ha' ⟨f₂ y, hy⟩, hc₂]

theorem sections_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ W : (A ⊗ T).left.Opens, (∀ a b : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = (A ◁ j₁).left.app W b → (A ◁ j₂).left.app W a = (A ◁ j₂).left.app W b → a = b) ∧ ∀ (V : (A ⊗ T₀).left.Opens) (h₁ : V ≤ (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W)) (h₂ : V ≤ (A ◁ k₂).left ⁻¹ᵁ ((A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ((A ⊗ T₁).left, (A ◁ j₁).left ⁻¹ᵁ W)) (a₂ : Γ((A ⊗ T₂).left, (A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left.appLE _ V h₁ a₁ = (A ◁ k₂).left.appLE _ V h₂ a₂ → ∃ a : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = a₁ ∧ (A ◁ j₂).left.app W a = a₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM W
  have : Flat (snd A T).left := inferInstanceAs (Flat (pullback.snd A.hom T.hom))
  have hw : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have hg : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hw]
  have hp : (A ◁ k₁).left ≫ (snd A T₁).left = (snd A T₀).left ≫ k₁.left := by
    rw [← Over.comp_left, ← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd]
  exact sections_of_squares hM (isPullback_whiskerLeft_snd_left A j₁)
    (isPullback_whiskerLeft_snd_left A j₂) (isPullback_whiskerLeft_snd_left A k₂) hg hp W

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDvrClosedFibreStalkUniformiserStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T → ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField), GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  first | exact @GlobalTheory.Desc.GenFibre.unif | exact GlobalTheory.Desc.GenFibre.unif | (intros; apply GlobalTheory.Desc.GenFibre.unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianLocusNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ZHAbLocusNonempty

theorem abLocus_nonempty : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (abLocus Zh.G).Nonempty := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO
  obtain ⟨z, hz⟩ := hO.ne
  refine ⟨z, ?_⟩
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

end GlobalTheory.ZHAbLocusNonempty
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E] (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f → ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  first | exact @GlobalTheory.Desc.semiAbelian_hom_extend_generic | exact GlobalTheory.Desc.semiAbelian_hom_extend_generic | (intros; apply GlobalTheory.Desc.semiAbelian_hom_extend_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadingsStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesRationality_back_from_movedReadings : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.UnframeForms.ratRow_back | exact GlobalTheory.UnframeForms.ratRow_back | (intros; apply GlobalTheory.UnframeForms.ratRow_back <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_polarization_pullback_stable : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback | exact GlobalTheory.Poinc.sharpOver_pullback | (intros; apply GlobalTheory.Poinc.sharpOver_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  first | exact @GlobalTheory.SiegLev.SQuot.eq_of_siegPB | exact GlobalTheory.SiegLev.SQuot.eq_of_siegPB | (intros; apply GlobalTheory.SiegLev.SQuot.eq_of_siegPB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F, Module.finrank ℤ T.D.toPre.X ≤ g := by
  first | exact @GlobalTheory.Poinc.Trait.finrank_le_of_three_le | exact GlobalTheory.Poinc.Trait.finrank_le_of_three_le | (intros; apply GlobalTheory.Poinc.Trait.finrank_le_of_three_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPiecesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  first | exact @GlobalTheory.ProdGlue.smooth_desc_of_isColimit | exact GlobalTheory.ProdGlue.smooth_desc_of_isColimit | (intros; apply GlobalTheory.ProdGlue.smooth_desc_of_isColimit <;> assumption)
end

