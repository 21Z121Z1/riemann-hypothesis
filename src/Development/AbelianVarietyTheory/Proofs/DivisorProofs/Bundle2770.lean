import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharacters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare

theorem q_comm_of_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a : D.P.A ⟶ D.P.A) (F : thickObj R I e G ⟶ thickObj R I e G)
    (hF : F.left ≫ g.pG.left = g.pG.left ≫ a.left) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    have := hF
    simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left] at this
    simpa [Category.assoc] using this
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
    have h1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w g.q
    have h2 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [h1, h2]

theorem torus_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  intro R _ _ I D e G _ _ g a a' _ _ h' u hu h₀ F hF
  have hb : IsMonHom ((Over.pullback (thick R I e)).map a) := inferInstance
  have hq := q_comm_of_isCoordEnd g a F hF.1
  have hd : (g.i ≫ F) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g.isKernel.w, Category.assoc, IsMonHom.one_hom]
  obtain ⟨t, ht⟩ : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X,
      t ≫ g.i = g.i ≫ F :=
    ⟨g.isKernel.lift _ _ hd, g.isKernel.lift_fst _ _ hd⟩
  refine ⟨t, fun χ => unit_ext fun y hy => ?_, ht.symm⟩
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB y
  have hJ : Good D.P.L y J := hJ
  have := g.q_hom
  have v₁ := val_torus g χ hJ t 1
  have v₂ := val_torus g (h' χ) hJ (𝟙 _) 1
  rw [_root_.mul_one, val_unit g _ hJ, _root_.mul_one] at v₁ v₂
  rw [ht] at v₁
  rw [Category.id_comp] at v₂
  have e1 : TorusCoord.im g g.i = 1 := (im_congr g (x' := 1) (by
    rw [g.isKernel.w, MonObj.one_comp, Hom.one_def])).trans (im_one g)
  have v₃ : val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) g.i.left y J = 1 :=
    (val_pull_lift u χ g.pG ((Over.map (thick R I e)).map g.i) hJ).trans
      ((congrArg _ e1).trans (val₂_axis D.P.isAb D.P.isLB a' a u hu h₀ hJ _))
  have v₄ := (hF.2 χ _ g.i.left y J hJ).trans ((congrArg₂ (· * ·) v₂ v₃).trans (_root_.mul_one _))
  refine (gm_res _ y (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans
    ((gm_pull (𝟙 _) t.left y ⊤ trivial _).trans ?_)
  rw [Category.id_comp]
  rw [Over.comp_left] at v₁
  exact v₁.symm.trans v₄

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gtCoord_overPoint_ext {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a a' : Z ⟶ thickObj R I e G)
    (hp : a.left ≫ g.pG.left = a'.left ≫ g.pG.left)
    (hv : ∀ (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      ∀ χ : D.X, val (g.t χ) a.left z J = val (g.t χ) a'.left z J) : a = a' := by
  have := g.i_hom
  have := g.q_hom
  have hq : a ≫ g.q = a' ≫ g.q := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  have hd : (a' * a⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, mul_inv_cancel]
    rfl
  let τ := g.isKernel.lift (a' * a⁻¹) (toUnit _) hd
  have hτ : τ ≫ g.i = a' * a⁻¹ := g.isKernel.lift_fst _ _ _
  have h1 : τ = 1 := by
    refine TorusPts.torusPt_ext fun χ => ?_
    refine congrArg Units.val (show pullU τ.left ⊤ (charUnit _ D.X χ) =
      pullU (1 : Z ⟶ splitTorus _ D.X).left ⊤ (charUnit _ D.X χ) from unit_ext fun z _ => ?_)
    choose J hJ using fun ψ : Z.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have k := (TorusCoord.val_torus_point_and_translate R I D e G g Z τ a z J hJ χ).2
    have k' := (TorusCoord.val_torus_point_and_translate R I D e G g Z 1 a z J hJ χ).2
    rw [hτ, inv_mul_cancel_right] at k
    rw [MonObj.one_comp, _root_.one_mul] at k'
    have k2 := mul_right_cancel (k.symm.trans ((hv z J hJ χ).symm.trans k'))
    exact (gm_pull (𝟙 Z.left) τ.left z ⊤ trivial _).trans (k2.trans
      (gm_pull (𝟙 Z.left) (1 : Z ⟶ splitTorus _ D.X).left z ⊤ trivial _).symm)
  rw [h1, MonObj.one_comp] at hτ
  exact (mul_inv_eq_one.1 hτ.symm).symm

theorem gtCoord_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  intro R _ _ I D e G _ _ g Z r r' hb hp hv
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  exact congrArg (fun φ => φ.left) (gtCoord_overPoint_ext g (Z := FinalForm) (Over.homMk r rfl) (Over.homMk r' hb.symm) hp hv)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0}) (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y), (∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e) → ∀ (V : G'.left.Opens) (W : Y.Opens), φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V → ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  first | exact @GlobalTheory.Mum.thick_preimage_eq | exact GlobalTheory.Mum.thick_preimage_eq | (intros; apply GlobalTheory.Mum.thick_preimage_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  first | exact @GlobalTheory.FormalAlg.LevSurj.ev_surjective | exact GlobalTheory.FormalAlg.LevSurj.ev_surjective | (intros; apply GlobalTheory.FormalAlg.LevSurj.ev_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_projective_relations : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | exact GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | (intros; apply GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullOfSval
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem toProj_secPull_of_gs {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} [Subsingleton Z] {A : LB Y} {A' : LB Y'}
    {N : ℕ} (σ : Fin (N + 1) → A.Sec) (τ : Fin (N + 1) → A'.Sec) (s : Y' ⟶ Sp R)
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Z ⟶ Y) (y : Z ⟶ Y')
    (H : ∀ z : Z, ∃ (a : A.ι) (a' : A'.ι) (c : (Z.presheaf.stalk z)ˣ), p z ∈ A.U a ∧ y z ∈ A'.U a' ∧
      ∀ i, gs p z _ ((σ i).f a) = c.val * gs y z _ ((τ i).f a')) :
    (∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧
      ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  have h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i) := by
    intro i z
    obtain ⟨a, a', c, ha, ha', e⟩ := H z
    rw [GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i,
      IsUnit.mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩
  have hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩
  refine ⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩
  obtain ⟨a, a', c, ha, ha', e⟩ := H z
  obtain ⟨W, hW, u, hu⟩ := Z.presheaf.exists_germ_eq c.val
  have hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U := fun hU x _ => (Subsingleton.elim z x) ▸ hU
  have hl : z ∈ (A.pull p).U fun _ => a := Set.mem_iInter.2 fun _ => ha
  refine ⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩
  obtain rfl : z = x := Subsingleton.elim _ _
  have e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a) :=
    (gs_res (𝟙 Z) z (hall hl) hW _).trans
      ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))
  have e₂ : gs (𝟙 Z) z W u = c.val := (gs_eq (𝟙 Z) z W hW u).trans hu
  have e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a') :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])
  rw [e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]

theorem toProj_secPull_of_sval : ∀ (R Ω : Type) [CommRing R] [Field Ω] (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (h : Y ⟶ X) (h' : Y' ⟶ X') (k N : ℕ) (σ : Fin (N + 1) → SecK L h k) (τ : Fin (N + 1) → SecK L' h' k) (s : Y' ⟶ Sp R) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Sp Ω ⟶ Y) (y : Sp Ω ⟶ Y'), L.IsLB → L'.IsLB → (∀ z J J', Good L z J → Good L' z J' → ∃ c : ((Sp Ω).presheaf.stalk z)ˣ, ∀ i, sval (σ i) p z J = c.val * sval (τ i) y z J') → (∀ i (z : Sp Ω), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧ ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  intro R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  refine toProj_secPull_of_gs σ τ s hτ p y fun z => ?_
  choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)
  obtain ⟨c, hc⟩ := H z J J' hJ hJ'
  exact ⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem torMatch_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (g₂ : V →+* V₂) (β₂ : G₂.left ⟶ G'.left), Function.Injective g₂ → (∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V)) → ∀ ρ ρ₂, TorMatch U U' g β ρ → TorMatch U' U₂ g₂ β₂ ρ₂ → TorMatch U U₂ (g₂.comp g) (β₂ ≫ β) (ρ₂.comp ρ) := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ hVb G' _ _ hG' D' A' U' g β V₂ _ _ _ hV₂b G₂ _ _ hG₂ D₂ A₂ U₂ g₂ β₂
    hg₂ hkV ρ ρ₂ h₁ h₂
  intro F _ _ _ _ hF k hk τ τ₂ q q₂ a a₂ hτ₂ hττ hqy hqt hq₂y hq₂t ha ha₂
  have hinj : Function.Injective ((algebraMap (FractionRing V₂) F).comp ((algebraMap V₂ (FractionRing V₂)).comp g₂)) :=
    (algebraMap (FractionRing V₂) F).injective.comp ((IsFractionRing.injective V₂ (FractionRing V₂)).comp hg₂)
  letI : Algebra (FractionRing V) F := (IsFractionRing.lift hinj).toAlgebra
  have hV : ∀ v, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V₂) F (algebraMap V₂ (FractionRing V₂) (g₂ v)) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  have hk' : IsUnit (k : V) := hkV k hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let τ' : Multiplicative D'.toPre.X →* Fˣ := τ₂.comp (AddMonoidHom.toMultiplicative ρ₂)
  have hτ' : τ' ^ k = 1 := MonoidHom.ext fun χ => DFunLike.congr_fun hτ₂ _
  obtain ⟨q', hq'y, hq't⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (k := k) τ' hτ'
  obtain ⟨hV', _⟩ := hVb
  obtain ⟨f', ⟨i', -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV' D' A' G' hG' U' F k hk1
  have e₁ := h₁ F (fun r => by rw [hF, hV]; rfl) k hk τ τ' q q' a (f' q') hτ' hττ hqy hqt hq'y hq't ha ((i' _ _).2 rfl)
  have e₂ := h₂ F hV k hk' τ' τ₂ q' q₂ (f' q') a₂ hτ₂ (fun _ => rfl) hq'y hq't hq₂y hq₂t ((i' _ _).2 rfl) ha₂
  rw [e₁, reassoc_of% e₂]

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGeneratorCharTrivial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := GlobalTheory.T.torsionPoint_locally_constant_complexAbelian A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc

theorem qk_lattice_oAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  intro E _ _ _ H V _ _ _ hV t P K _ _ _ m a pk pk' x x' hm hx hx' hxx'
  obtain ⟨h1, h2, h3⟩ := hV
  have hT : P.TorsionIso := GlobalTheory.GeneratorsCompare.torsionIso P
  obtain ⟨f, hf, -, heq, -, hact, -⟩ := hT K m hm
  letI := H.starRing
  obtain ⟨p'', hp''⟩ := qkAct_exists GlobalTheory.lawsAndExpansions.1.1.globalFns P.D.tau_bimult P.oD a pk
  have e1 : f p'' = x' := by
    rw [hact a pk p'' hp'', ← (hf pk x).1 hx, hxx']
  have e2 : f p'' = f pk' := by rw [e1, ← (hf pk' x').1 hx']
  obtain ⟨z₂, hz₂, -⟩ := (heq p'' pk').1 e2
  obtain ⟨q, hq, -, z₁, hz₁, -⟩ := hp''
  exact ⟨z₁ + z₂, by rw [hz₂, hz₁, hq, smul_add, add_assoc]⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelActionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_class_image_eq_level_action : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  first | exact @GlobalTheory.TorsSpec.class_move | exact GlobalTheory.TorsSpec.class_move | (intros; apply GlobalTheory.TorsSpec.class_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem val_eq_of_maps_pullAlong {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (F : X ⟶ X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (W : LB.Iso (LB.LinComb L φ ε) (LB.LinComb (L.pull F) φ ε)) (a t : LB.Gen (LB.LinComb L φ ε))
    (f f' : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k) (hψ' : ∀ k, φ k ≫ F = f' ≫ φ k)
    (h : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f φ ε φ hψ t)) (h' : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f' φ ε φ hψ' t))
    (z : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L z J) : val t f z J = val t f' z J := by
  let jj : K → (L.pull F).ι := fun k _ => J (φ k ≫ F)
  let q : K → L.ι := fun k => J (φ k)
  have m₁ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ (φ k ≫ F)
  have m₂ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L φ q := Set.mem_iInter.2 fun k => hJ (φ k)
  have m : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q := ⟨m₁, m₂⟩
  have key : ∀ (f : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k),
      val t f z J = gm (𝟙 Y) z _ (res (inf_le_left : LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q ≤ _)
        ((GeneratorPullback.pullAlong L F f φ ε φ hψ t).s jj)) := by
    intro f hψ
    rw [val_of t f z J (fun k => J (φ k ≫ F)) (fun k => by rw [hψ k])]
    exact ((gm_res (𝟙 Y) z _ m _).trans ((gm_res (𝟙 Y) z _ m₁ _).trans
      (gm_pull (𝟙 Y) f z _ (@GeneratorPullback.pullAlong_le _ _ _ _ L _ _ F f φ φ hψ jj z m₁) _))).symm
  rw [key f hψ, key f' hψ']
  exact congrArg (gm (𝟙 Y) z _) ((h (jj, q)).trans (h' (jj, q)).symm)

theorem gtCoord_val_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J :=
  fun g F _ f f' x hψ hψ' h h' z J hJ => val_eq_of_maps_pullAlong F _ Oinvε _ (g.t x) (g.t x) f f' hψ hψ' h h' z J hJ

end GlobalTheory.Mum
end
end

