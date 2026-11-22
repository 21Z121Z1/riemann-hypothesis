import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.LowSame

open GlobalTheory.SiegLev GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_cls_lev {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h n ζ s) (hζ : IsUnit ζ) (hnB : IsUnit (n : B)) (hn : 3 ≤ n) (hc : c.Principal)
    {A' : Over S'} [GrpObj A'] (hab' : IsAbelianScheme A') (f : S' ⟶ S) (φ φ' : A'.left ⟶ c.A.left)
    (g : IsGrpPullback A' c.A f φ) (g' : IsGrpPullback A' c.A f φ')
    (hcl : pull φ (cls c.diag (pull_isLB c.isLB _)) = pull φ' (cls c.diag (pull_isLB c.isLB _)))
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (l : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (l' : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left) :
    φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 A' hab' σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback A' j
    have := hab'.smooth
    have := hab'.proper
    have := hab'.geomConnected
    have := hab'.comm
    have hab : IsAbelianScheme ((Over.pullback j).obj A') :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A'.hom j); infer_instance
        proper := by change IsProper (pullback.snd A'.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A'.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := hnB.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ hcl) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion hζ c g lv l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.LowSame

namespace GlobalTheory.LowSame

open GlobalTheory.SiegelPullComp

theorem eq_of_presentations : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  intro o _ ζ h n F' hn hζ hno V _ _ _ A _ _ t₁ t₂ a₁ a₂ aa₁ aa₂ ha₁ ha₂ sq₁ sq₂ hP hs F _ _ hlev
  let c' := GlobalTheory.LowChart.siegPull F'.univ t₁ (t₁ ≫ F'.s) rfl
  have m₁ : SiegPB c' F'.univ t₁ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  obtain ⟨pφ, pφ₂, gp, psq, pw, pl⟩ := id m₁
  let F₀ : c'.A.left ⟶ A.left := ha₁.1.lift pφ c'.A.hom gp.1.w
  have hF : F₀ ≫ a₁ = pφ := ha₁.1.lift_fst _ _ _
  have hFw : F₀ ≫ A.hom = c'.A.hom ≫ 𝟙 _ := (ha₁.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hF₀ : IsGrpPullback c'.A A (𝟙 _) F₀ :=
    ha₁.cancel (gp.congr (Category.id_comp _).symm hF.symm) hFw
  have gφ : IsGrpPullback c'.A F'.univ.A t₂ (F₀ ≫ a₂) := (hF₀.comp ha₂).congr (Category.id_comp _) rfl
  let U : Over.mk ((c'.A ⊗ c'.A).hom ≫ 𝟙 _) ⟶ A ⊗ A :=
    lift (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A))
  let F₂ : (c'.A ⊗ c'.A).left ⟶ (A ⊗ A).left := U.left
  have h₁ : F₂ ≫ (fst A A).left = (fst c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₂ : F₂ ≫ (snd A A).left = (snd c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₃ : F₂ ≫ aa₁ = pφ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst F'.univ.A F'.univ.A).left = _ ≫ (fst F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.1, ← Category.assoc, h₁, Category.assoc, hF, psq.1]
    · show (_ ≫ _) ≫ (snd F'.univ.A F'.univ.A).left = _ ≫ (snd F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.2, ← Category.assoc, h₂, Category.assoc, hF, psq.2]
  have sq : IsSquare (F₀ ≫ a₂) (F₂ ≫ aa₂) :=
    ⟨by rw [Category.assoc, sq₂.1, ← Category.assoc, h₁, Category.assoc],
     by rw [Category.assoc, sq₂.2, ← Category.assoc, h₂, Category.assoc]⟩
  have hU := F'.univ.isLB
  have iso : LBIso c'.P (F'.univ.P.pull (F₂ ≫ aa₂)) := by
    rw [← h₃] at pw
    refine pw.trans c'.isLB (pull_isLB hU _) (pull_isLB hU _) ?_
    refine (iso_pull_pull hU aa₁ F₂).symm.trans (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    refine (iso_pull F₂ hP).trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    exact iso_pull_pull hU aa₂ F₂
  have lev : ∀ a, (c'.lev a).left ≫ (F₀ ≫ a₂) = t₂ ≫ (F'.univ.lev a).left := by
    intro a
    have hσ : ((c'.lev a).left ≫ F₀) ≫ A.hom = 𝟙 _ := by
      rw [Category.assoc, hFw, Category.comp_id]
      exact Over.w (c'.lev a)
    have hσ₁ : ((c'.lev a).left ≫ F₀) ≫ a₁ = t₁ ≫ (F'.univ.lev a).left := by
      rw [Category.assoc, hF]; exact pl a
    obtain ⟨x, hx₁, hx₂⟩ := hlev a
    have hx : x.left = (TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀ := by
      apply ha₁.1.hom_ext
      · rw [hx₁, Category.assoc, hσ₁]
      · rw [Over.w x, Category.assoc, hσ]
        exact (Category.comp_id _).symm
    have := F'.univ.ab.proper
    have : IsReduced (𝟙_ (Over (Sp V))).left := (inferInstance : IsReduced (Sp V))
    have := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated F'.univ.A.hom ?_ (DegPre.jFR (R := V) F) ?_
    · rw [Category.assoc, Category.assoc, ha₂.1.w, ← Category.assoc, ← Category.assoc, hσ, Category.id_comp,
        Category.assoc, Over.w (F'.univ.lev a)]
      rfl
    · rw [← Category.assoc]
      show ((TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀) ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev a).left
      rw [← hx]
      exact hx₂
  have m₂ : SiegPB c' F'.univ t₂ := ⟨F₀ ≫ a₂, F₂ ≫ aa₂, gφ, sq, iso, lev⟩
  have ht : t₁ = t₂ := F'.inj V t₁ t₂ (t₁ ≫ F'.s) c' hs m₁ m₂
  subst ht
  refine ⟨rfl, ?_⟩
  have hcl := (GlobalTheory.SiegRigid.pull_cls_diag psq pw).trans (GlobalTheory.SiegRigid.pull_cls_diag sq iso).symm
  have e := eq_of_cls_lev F'.univ hζ hno hn F'.princ c'.ab t₁ pφ (F₀ ≫ a₂) gp gφ hcl c'.lev pl lev
  have : IsIso F₀ := hF₀.1.isIso_fst_of_isIso
  rw [← hF] at e
  exact (cancel_epi F₀).1 e

end GlobalTheory.LowSame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallApplyHodgePrimitiveEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem eq_zero_of_forall_apply_psi_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → ∀ x : G.Lie, (∀ c, x (ψ c) = 0) → x = 0 := by
  intro p _ R _ N hN A _ hA hL G t ψ hψ x hx
  have : IsAdicComplete (Ideal.span {(p : R)}) R :=
    GlobalTheory.isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨v, hv⟩ := exists_lieCorr_of_pow_eq_zero p R N hN A G t x
  obtain ⟨h, hh⟩ := hL.2 v hv.1

  have hFil : h ∈ Fil A := by
    rw [mem_Fil]
    intro f hf
    have hF : (⟨_, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
      change Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 _)
      rw [hodgeFiltration_eq_range]
      exact LinearMap.mem_range_self _ f
    rw [hh.2 f hf, ← lie_psi_cl_eq_tanVal p R N hN A hA G t ψ hψ f hf hF x v hv]
    exact hx _

  have hv1 : v = 1 := (hL.1 h).unique hh (isLieImage_one_iff.mpr hFil)
  subst hv1
  exact hv.unique_left TorsionTower.lieCorr_zero

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnitStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_bound_length_unit : Size → Covers fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  first | exact @GlobalTheory.ThetaSizeBounds.params_sqrt_bounds | exact GlobalTheory.ThetaSizeBounds.params_sqrt_bounds | (intros; apply GlobalTheory.ThetaSizeBounds.params_sqrt_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X, (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | exact GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | (intros; apply GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero : ∀ (X : Scheme.{0}), Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → ∀ x : X,
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  first | exact @GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | exact GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | (intros; apply GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparatingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSections_vanishing_origin_separating : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB → Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)), (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧ ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  first | (exact @GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (exact GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (intros; apply GlobalTheory.RelAmpleSep.exists_sec_sep_origin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dm : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {T : Formalism.L2.Pj.CDVR}

theorem tateCl_of (β : O →+* c.F) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
      ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre oD F),
        (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧
        (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧
        ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a)) :
    TateCl D oD hϖ Dm β b hdiv pA pM := by
  intro F _ _ _ z hz
  letI := H.starRing
  obtain ⟨I, hζ, e₂, e₃⟩ := h F z hz
  have hw := GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)
  have ht := isScalarForm_tF D oD hϖ
  have hq := psiRel0 (H := H) D hϖ
  have hR := isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (dvd_refl l.M') hdiv)
  let s : D.toPre.X → D.toPre.X → Fˣ := fun y x =>
    Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (rF D hϖ l.M' y x)
  have hs : IsRootForm (𝓞 E) l.M' (tF D hϖ) s :=
    ⟨hR.1.map _, fun y x => by
      show (Units.map _ _) ^ _ = _
      rw [← map_pow, hR.2 y x]
      rfl⟩
  obtain ⟨s', I', s₁, -, s₃, s₄, s₅⟩ := exists_tateIsoQ_twist D.tau_bimult hw ht oD l.M' s hs I
  have lev : ∀ {k : ℕ} (hk : 0 < k) (hd : k ∣ l.M') (p : QkPt D.toPre (FractionRing T.V) k) (v : Dm.La),
      (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv D.toPre F q (I.ev k v)) → ∀ q',
      QkExt (algebraMap _ F) (qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) _ p) q' →
      QkPt.Equiv (D0 (H := H) D hϖ) F q' (I'.ev k v) := by
    intro k hk hd p v he q' hq'
    obtain ⟨q, rfl⟩ := (qkScaleEquiv hw ht hq (s₁ k hk) _).surjective q'
    have e := qkRel_qkScaleEquiv (D := D.toPre) (hψ := (D0 (H := H) D hϖ).psi_gen) hw ht hq (s₁ k hk) q
    refine e.equiv hw ht hq (s₁ k hk) (s₅ k hk v) (he q (QkRel.qkExt_of (fun y x => ?_)
      (qkRel_qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) p) e hq'))
    rw [s₃ k hk hd]
    show (Units.map _ _) ^ _ = _
    rw [← map_pow]
    congr 1
    obtain ⟨j, hj⟩ := dvd_of_dvd D hϖ (dvd_refl l.M') hdiv y x
    obtain ⟨i, hi⟩ := hd
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
    have hi0 : (i : ℤ) ≠ 0 := by
      rintro h
      have : i = 0 := by exact_mod_cast h
      rw [this, mul_zero] at hi
      omega
    simp only [rF, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hj, hi, Nat.mul_div_cancel_left _ hk]
    push_cast
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hi0), _root_.mul_assoc, Int.mul_ediv_cancel_left _ hk0]
    ring
  exact ⟨I', by rw [s₄]; exact hζ, fun v => lev l.A_pos (Nat.dvd_lcm_right l.M l.A) _ v (e₂ v),
    fun v _ q hq => lev (lt_of_lt_of_le (by decide) l.three_le) (Nat.dvd_lcm_left l.M l.A) _ v (e₃ v) q hq⟩

end GlobalTheory.TraitArc

open GlobalTheory.TraitArc in

theorem GlobalTheory.TraitArc.exists_input_recovering : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP l c O _ β hβ V₁ _ _ _ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
  obtain ⟨T, ρ, b, ϖ, D', hρ, hρf, hb, hϖ, ⟨hD⟩, hdvd, hrat⟩ :=
    GlobalTheory.T.exists_traitExtension_divisible_valuationForm R D O V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁ (2 * l.M') (by omega)
  have hBase : Base R := ⟨by haveI := hR.1; exact ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩, hR.2.2⟩
  obtain ⟨inst, o', hP'⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hBase E H Dm D o hP T.V ρ hρ D' ⟨hD⟩
  letI := inst
  have hX' : Nontrivial D'.toPre.X := hD.xe.toEquiv.nontrivial
  have hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D' hϖ a a' := fun a a' => by
    have := hdvd _ (isQ_qv D' hϖ) a a'
    exact_mod_cast this
  obtain ⟨pA, pM, hT⟩ := GlobalTheory.T.exists_rational_tate_pairs_unitaryType E H Dm l c O β hβ T b hb D' o' hP' (fun k hk => hrat k (hk.mul_left 2))
  have hLie : LieCl D' o' Dm β b := by
    intro F _ _ _ r _ τ
    obtain ⟨n, h₁, h₂⟩ := (hP'.2.2.2 F).1 τ
    refine ⟨n, h₁, ?_⟩
    split_ifs
    · exact h₂
    · exact h₂.trans hP'.1
  have hTate := tateCl_of β b D' o' hϖ hdiv pA pM hT
  refine ⟨T.V, T.cr, T.dom, inferInstance, ρ, b, ϖ, arc D' o' hϖ β b hX' hP'.2.2.1 hdiv pA pM hLie hTate,
    ⟨T.dvr, T.cpl, T.ch0⟩, hρ, hρf, hϖ, ?_⟩
  intro Xo Y y hy
  obtain ⟨t, m, P, ⟨hD₂⟩⟩ := GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser E H Dm l c O β T b D' o' ϖ hϖ hX' hP'.2.2.1 hdiv pA pM hLie hTate Xo Y y hy
  refine ⟨t, m, P, ?_⟩
  have := GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R T.V T.V ρ (RingHom.id T.V) D.toPre D'.toPre P.D.toPre
    Function.injective_id ⟨hD⟩ ⟨hD₂⟩
  rwa [RingHom.id_comp] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverseStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_model_regular_function_or_inverse : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  first | exact @GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | exact GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | (intros; apply GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartDensBc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem exists_chart_dens_bc : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) (D : ℕ) (c : AlgChart p (τ.comp ρ) D) (z : CxPts q τ), bcPt hp.w τ z ∈ c.e.source → ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) ∧ ∀ L : Fin D → MLine p (τ.comp ρ), dens (fun i => (L i).bc hp.w τ) c' w = dens L c (bcPt hp.w τ w) := by
  intro k K _ _ ρ X G p q j hp τ D c z hz
  have hm : ∀ w, (bcPt hp.w τ w).1 = w.1 ≫ j := fun _ => rfl
  obtain ⟨c₀, hz₀, h, hx⟩ := c.exists_baseChange hp hm hz
  let c' := c₀.restr (bcPt hp.w τ ⁻¹' c.e.source) (c.e.open_source.preimage (continuous_bcPt hp.w τ))
  have H : ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) := by
    intro w hw
    rw [AlgChart.restr_source] at hw
    refine ⟨hw.2, ?_⟩
    change c₀.e w = _
    ext a
    rw [c.apply_eq _ hw.2, c₀.apply_eq _ hw.1, hx, ev_appLE_of_comp hm h _ (c₀.source_subset hw.1)]
  refine ⟨c', by rw [AlgChart.restr_source]; exact ⟨hz₀, hz⟩, fun w hw => ⟨(H w hw).1, (H w hw).2, fun L => ?_⟩⟩
  have hw' := (H w hw).1
  have key (N : MLine p (τ.comp ρ)) :
      c'.hess (N.bc hp.w τ).φ (pick (N.bc hp.w τ).φ.isLB w) w =
        c.hess N.φ (pick N.φ.isLB (bcPt hp.w τ w)) (bcPt hp.w τ w) := by
    have hj := mem_of_mem_linComb (m := fun _ => bcPt hp.w τ w) (fun _ => rfl)
      (mem_pick (N.bc hp.w τ).φ.isLB w) PUnit.unit
    rw [c.hess_eq N.cInf hw' hj (mem_pick _ _), AlgChart.hess,
      AlgChart.hess, ← (H w hw).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hw)] with v hv
    obtain ⟨h₁, h₂⟩ := H _ (c'.e.map_target hv)
    rw [c'.e.right_inv hv] at h₂
    have e₁ : c.e.symm v = bcPt hp.w τ (c'.e.symm v) := (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
    rw [e₁]
    simp [MLine.bc, Weight.linComb]
  simp only [dens, key]

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedFibre_iso_torusExtension_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.closedFibre_iso | exact GlobalTheory.Mum.closedFibre_iso | (intros; apply GlobalTheory.Mum.closedFibre_iso <;> assumption)
end

