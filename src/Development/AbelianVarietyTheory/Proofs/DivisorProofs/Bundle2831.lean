import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationCompIdPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullUnifId

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW' {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R'' : Type} [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    (hj : Function.Injective j) {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D')
    (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_valW' D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def pullIdIso (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (Over.pullback (specOf (RingHom.id R'))).obj ((Over.pullback (specOf φ)).obj G) ≅ (Over.pullback (specOf φ)).obj G :=
  Over.isoMk (pullbackLeftPullbackSndIso G.hom (specOf φ) (specOf (RingHom.id R')) ≪≫
    pullback.congrHom rfl (by rw [specOf_id, Category.id_comp])) (by
      show _ ≫ pullback.snd _ _ = pullback.snd _ _
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
      erw [pullback.lift_snd]
      simp)

theorem pullIdIso_fst (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (pullIdIso φ G).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst _ (specOf (RingHom.id R')) ≫ pullback.fst G.hom (specOf φ) := by
  simp only [pullIdIso, Over.isoMk_hom_left, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
  erw [pullback.lift_fst]
  simp

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

open GlobalTheory.PsiEvenPull (proj)

theorem isPullUnif_comp_id : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R')
    (D : DegData R I) (D' D'' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
    (hid : IsPullDeg (RingHom.id R') D'.toPre D''.toPre)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' A'' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (G' G'' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (bc' : G'' ≅ (Over.pullback (specOf (RingHom.id R'))).obj G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') (U'' : Unif I' D'' A'' G''),
    IsPullUnif φ hD bc U U' → IsPullUnif (RingHom.id R') hid bc' U' U'' →
    ∃ (h : IsPullDeg φ D.toPre D''.toPre) (bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G),
      IsPullUnif φ h bc'' U U'' ∧ (∀ x, h.xe x = hD.xe (hid.xe x)) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        hid.e.hom.left ≫ pullback.fst D'.toPre.P.A.hom (specOf (RingHom.id R')) ≫
          hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) ∧
      bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
        bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (IsMonHom bc.hom → IsMonHom bc'.hom → IsMonHom bc''.hom) := by
  intro R R' _ _ _ _ I I' φ D D' D'' hD hid A A' A'' G _ _ G' G'' _ _ _ _ bc bc' U U' U'' H₁ H₂
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := exists_isPullDeg_comp (j := RingHom.id R') (fun _ _ h => h) hD hid
  let bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G :=
    bc' ≪≫ (Over.pullback (specOf (RingHom.id R'))).mapIso bc ≪≫ pullIdIso φ G
  have hb : bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
      bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    have := pullIdIso_fst φ G
    simp only [bc'', Iso.trans_hom, Over.comp_left, Category.assoc, this, Functor.mapIso_hom]
    congr 1
    simp only [Over.pullback, pullback.map]
    erw [pullback.lift_fst_assoc]
    rfl
  refine ⟨r, bc'', GalMul.isPullUnif_comp (i := φ) (j := RingHom.id R') r₁ r₂ r₃ T
      (hb.trans (Category.assoc _ _ _).symm) H₁ H₂, fun x => congrArg (fun e => e x) r₂,
      r₁.trans (Category.assoc _ _ _), hb, fun m₁ m₂ => ?_⟩
  have p₁ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have p₂ : IsGrpPullback G'' G' (specOf (RingHom.id R')) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) :=
    ((isGrpPullback_of_iso bc').comp (isGrpPullback_pullback G' (specOf (RingHom.id R')))).congr (Category.id_comp _) rfl
  have p : IsGrpPullback G'' G (specOf φ) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    (p₂.comp p₁).congr (by rw [specOf_id, Category.id_comp]) (Category.assoc _ _ _)
  obtain ⟨e, he, hf⟩ := grpPullback_iso p (isGrpPullback_pullback G (specOf φ))
  have : bc''.hom = e.hom := by
    ext1
    apply pullback.hom_ext
    · exact hb.trans hf.symm
    · exact (Over.w bc''.hom).trans (Over.w e.hom).symm
  rw [this]
  exact he

end GlobalTheory.PullUnifId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationOfLineBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section
namespace GlobalTheory.Mum

theorem isPullUnif_of_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → ∃ (h : IsPullDeg ρ D₁.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf ρ)).obj G), bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = β ∧ IsPullUnif ρ h bc U₁ U' := by
  intro R _ _ _ hRb R' _ _ _ ρ hfin D' A' G' _ _ hsa' U' G _ _ β hsa hgp A D₁ U₁ hL
  obtain ⟨hR', hinj, hfinite⟩ := hfin
  have hR := hRb.1
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap ρ))
  subst hbc
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    GlobalTheory.ResidueGalois.map_maximalIdeal_le ρ hfinite.to_isIntegral
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₁.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback G' (jK R')).comp hgp).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₁.LG.L.pull (pullback.fst G'.hom (jK R') ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₁.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₁.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₁.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₁.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G :=
    (cubeMapOf hgp).e_comm
  obtain ⟨w₀, hw₀⟩ := hL
  have hσ : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨wL, gL, pL⟩ := GlobalTheory.UnifPreCompare.exists_rigidified U₁.LG.isLB U'.LG.isLB G'.hom (eSec G') hσ w₀ hw₀
    U'.LG.rig U'.LG.rigGen U₁.LG.rig U₁.LG.rigGen (specOf ρ) he
  have mL : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) (specOf ρ) he U₁.LG.L U₁.LG.rig) :=
    (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U₁.LG.rig (specOf ρ) _
      (rigPull_le (G' := G') (G := G) _ (specOf ρ) he U₁.LG.L) (fun _ => rfl)).2 pL
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists R (maximalIdeal R) hR D₁
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D'', hD₁, U'', hLG, -, H₁⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds R R' (maximalIdeal R) (maximalIdeal R')
    hR hR' ρ hI D₁ A G hsa U₁ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gL mL
  obtain ⟨wL₀, g₀, m₀⟩ := exists_iso_of_eq hLG.symm
  have h6 := GlobalTheory.unifUniq GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample
  obtain ⟨hD₂, hlev, -⟩ := h6 R' (maximalIdeal R') hR' D'' D' A'' A' G' hsa' U'' U' wL₀ g₀ m₀
  have hs := specOf_id R'
  haveI mR : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, -, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl G')).congr hs.symm rfl)
    (isGrpPullback_pullback G' (Out.specOf (RingHom.id R')))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G'.hom (Out.specOf (RingHom.id R')) = 𝟙 _ := hbc₀
  have H₂ := isPullUnif_of_uniq U'' U' hD₂ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp hinj (fun _ _ h => h) hD₁ hD₂
  have hb : bc.hom.left ≫ pullback.fst G.hom (specOf ((RingHom.id R').comp ρ)) =
      (bc₀.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) ≫
        (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    rw [hbc₀', Category.id_comp]
  exact ⟨r, bc, rfl, GalMul.isPullUnif_comp r₁ r₂ r₃ T hb H₁ H₂⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformised
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPer

theorem isReg_fderiv_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  intro A _ g L u hA U b w
  have hs := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := (GlobalTheory.TorusTransfer.tangent_bijective u hs).2 w
  obtain ⟨d, -, hdv⟩ := GlobalTheory.KS.exists_locDer_of_isDiff A u w v hv hd
  exact ⟨d U b, fun z hz => (hdv U b z hz).symm⟩

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

set_option backward.isDefEq.respectTransparency false in

theorem Taut.isRegularLocalRing_and_isRelParam : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ C : Taut (zetaAway n) g n φ, IsRegularLocalRing C.R ∧ CharZero C.R ∧ Function.Injective C.b ∧ C.b.Flat ∧ IsRelParam C.b C.t ∧ IsRegularLocalRing (C.R ⧸ ((maximalIdeal C.R).comap C.b).map C.b) := by
  intro g n φ _ C
  haveI : IsNoetherianRing C.W := C.noeth
  haveI : IsLocalHom C.iw := C.ψ_loc
  set X := (LowChart.powA C.F C.T.r).left with hX
  set π := LowChart.toO C.F C.T.r with hπ
  set y := C.u (closedPoint C.W) with hy
  let φ₀ : X.presheaf.stalk y →+* C.W := (Scheme.stalkClosedPointTo C.u).hom
  let σ := (π.stalkMap y).hom
  let L := Localization.AtPrime (π y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of (cycAway n)) (π y)
  let ρ : cycAway n →+* X.presheaf.stalk y := σ.comp (e.inv.hom.comp (algebraMap (cycAway n) L))
  have h3 : (Sp (cycAway n)).fromSpecStalk (π y) = Spec.map e.inv ≫ spMap (algebraMap (cycAway n) L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (π y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := π y)).symm
  have hb : C.T.b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk C.u
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y)
    have key : spMap C.T.b = spMap (φ₀.comp ρ) := by
      rw [← C.u_base, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (π y).asIdeal = (maximalIdeal C.W).comap C.T.b := by
    have : π y = spMap C.T.b (closedPoint C.W) := by
      rw [hy, ← C.u_base, Scheme.Hom.comp_apply]
    rw [this]; rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk C.F y
  have het := C.u_et
  haveI hW : IsRegularLocalRing C.W := by
    letI : Algebra (X.presheaf.stalk y) C.W := φ₀.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y) C.W := het.1
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm
  obtain ⟨hRreg, hRdom⟩ := isRegularLocalRing_and_isDomain_of_isComplAt C.W (Fin C.m ⊕ Fin C.N) C.R C.ψ C.compl C.ψ_loc
  have hρspec : spMap ρ = X.fromSpecStalk y ≫ π := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y), h3]
    simp only [spMap, ρ, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
  have hflatρ : ρ.Flat := by
    haveI := GlobalTheory.SmoothStalkNormal.flat_fromSpecStalk' X y
    have h : Flat (spMap ρ) := by rw [hρspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  have hiwflat : C.iw.Flat :=
    (show (algebraMap C.W (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W)).Flat from
      RingHom.flat_algebraMap_iff.mpr inferInstance).comp C.compl.2.2.1
  have hbeq : C.b = C.iw.comp (φ₀.comp ρ) := by rw [← hb]; rfl
  have hbflat : C.b.Flat := by rw [hbeq]; exact (hflatρ.comp het.1).comp hiwflat
  have hinj : Function.Injective C.b := GlobalTheory.SmoothStalkNormal.injective_of_flat_of_isDomain C.b hbflat
  have hmW : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := IsLocalRing.maximalIdeal_comap C.iw
  have h𝔮 : (maximalIdeal C.R).comap C.b = (π y).asIdeal := by
    rw [hq, show C.b = C.iw.comp C.T.b from rfl, ← Ideal.comap_comap, hmW]
  have hle : ((maximalIdeal C.R).comap C.b).map C.b ≤ (maximalIdeal C.W).map (C.ψ.comp MvPolynomial.C) := by
    rw [show C.b = C.iw.comp C.T.b from rfl, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.2 ?_)
    rw [← Ideal.comap_comap, hmW]
  refine ⟨hRreg, charZero_of_injective_ringHom hinj, hinj, hbflat, ⟨fun k => C.bd k, fun c hc k =>
    cotangent_indep_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc C.m ⟨Sum.inl, Sum.inl_injective⟩ (fun k => C.bd k) c
      (sup_le_sup_left hle (maximalIdeal C.R ^ 2) hc) k⟩, ?_⟩
  have hfib := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal (Sp (cycAway n)) X π y
  set I := (maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y))).map σ with hIdef
  have hI : I = (π y).asIdeal.map ρ := by
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hmL : maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y)) = (maximalIdeal L).map e.inv.hom :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [hIdef, hmL, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    rfl
  set 𝔭 := I.map φ₀ with h𝔭def
  have h𝔭 : 𝔭.map C.iw = ((maximalIdeal C.R).comap C.b).map C.b := by
    rw [h𝔭def, hI, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hbeq, h𝔮]
  have hIm : I ≤ maximalIdeal (X.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap σ).ge
  have h𝔭m : 𝔭 ≤ maximalIdeal C.W := het.2.1 ▸ Ideal.map_mono hIm
  have h𝔭ne : 𝔭 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h𝔭m
  haveI : Nontrivial (C.W ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.2 h𝔭ne
  haveI : IsLocalRing (C.W ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hreg𝔭 : IsRegularLocalRing (C.W ⧸ 𝔭) := by
    let χ : (X.presheaf.stalk y ⧸ I) →+* (C.W ⧸ 𝔭) := Ideal.quotientMap 𝔭 φ₀ Ideal.le_comap_map
    have hχflat : χ.Flat := GlobalTheory.Pat.flat_quotientMap_map φ₀ het.1 I
    letI : Algebra (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := χ.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := hχflat
    have hcomm : (Ideal.Quotient.mk 𝔭).comp φ₀ = χ.comp (Ideal.Quotient.mk I) := by
      ext a; simp [χ]
    have hmax : maximalIdeal (C.W ⧸ 𝔭) = (maximalIdeal (X.presheaf.stalk y ⧸ I)).map (algebraMap _ _) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective, ← het.2.1,
        ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
        Ideal.map_map, hcomm]
      rfl
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ _ hmax
  have hfin := isRegularLocalRing_quotient_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc 𝔭 h𝔭ne hreg𝔭
  rwa [show C.ψ.comp MvPolynomial.C = C.iw from rfl, h𝔭] at hfin

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem prod_support_eq {U : Type} [CommGroup U] {r : ℕ} (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

theorem triv_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' →
    GlobalTheory.TensBal.Triv T (c + c') := by
  intro R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom T v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen D.P.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']
    exact (Finsupp.prod_add_index' (f := c) (g := c')
      (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n))
      (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm

end GlobalTheory.TensBal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorNeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBalNeg

theorem triv_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  intro R _ _ D D' r W T c ⟨Ξ, hΞ, h1, h2⟩
  have hF : FormEq (fun v : c.support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen D.P.isLB hF (LB.invGen D.P.L _ _ Ξ) (LB.isGen_invGen D.P.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y', Finsupp.support_neg, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finsupp.neg_apply, neg_neg, zpow_neg, inv_inv]

end GlobalTheory.TensBalNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  first | exact @GlobalTheory.Mum.unit_nonfield | exact GlobalTheory.Mum.unit_nonfield | (intros; apply GlobalTheory.Mum.unit_nonfield <;> assumption)
end

