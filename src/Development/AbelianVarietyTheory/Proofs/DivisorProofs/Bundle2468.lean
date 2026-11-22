import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftClosed
open GlobalTheory.QCoh GlobalTheory.Twist

theorem res_eq {X : Scheme.{0}} (I : X.IdealSheafData) {V W : X.Opens} (h : W ≤ V)
    (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W)
      (resM ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) h
        ((structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ V)).symm x)) =
      (I.subscheme.presheaf.map (homOfLE (fun _ hz => h hz :
        I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ V)).op).hom x := rfl

theorem smul_eq {X : Scheme.{0}} (I : X.IdealSheafData) {W : X.Opens} (r : Γ(X, W))
    (m : Γ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme), W)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) (r • m) =
      (I.subschemeι.app W).hom r * structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) m := rfl

theorem epi_toSubscheme {X : Scheme.{0}} (I : X.IdealSheafData) : Epi (toSubscheme I) := by
  rw [epi_iff_forall_affine]
  intro U hU y
  obtain ⟨f, hf⟩ := I.subschemeι_app_surjective ⟨U, hU⟩ ((structureModuleSectionsEquiv _) y)
  refine ⟨(structureModuleSectionsEquiv U).symm f, ?_⟩
  apply (structureModuleSectionsEquiv _).injective
  rw [← hf]
  rfl

theorem exists_twistSec_of_sec {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec) :
    ∃ b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤),
    ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)) := by
  refine ⟨mkSec (fun i => (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).symm
    ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))) ?_,
    fun i => ?_⟩
  · intro i j
    apply (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j))).injective
    dsimp only
    rw [smul_eq, res_eq, res_eq]
    have hi : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => i) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.1.2
    have hj : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => j) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.2
    refine fn_ext fun z hz => ?_
    have e1 := gs_res (𝟙 I.subscheme) z (fun _ hz => hz.1 : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    have e1' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i)) hz.1 (σ.f (fun _ => i))
    have e2 := gs_res (𝟙 I.subscheme) z (fun _ hz => ⟨hz.1.1, hz.2⟩ : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j))).op).hom (σ.f (fun _ => j)))
    have e2' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j)) ⟨hz.1.1, hz.2⟩ (σ.f (fun _ => j))
    have hz' : I.subschemeι z ∈ M.U i ⊓ M.U j := ⟨hz.1.2, hz.2⟩
    have e3 := gs_pull (𝟙 I.subscheme) I.subschemeι z (⊤ ⊓ M.U i ⊓ M.U j) hz (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g i j : Γ(X, M.U i ⊓ M.U j)))
    have e4 := gs_res (𝟙 I.subscheme ≫ I.subschemeι) z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) hz (M.g i j : Γ(X, M.U i ⊓ M.U j))
    have e5 := gs_unit (𝟙 I.subscheme ≫ I.subschemeι) z _ hz' (M.g i j)
    have e6 := gs_compat σ (𝟙 _) z (hi z hz) (hj z hz)
    have e7 := gm_pull_g M I.subschemeι (𝟙 _) z (fun _ => i) (fun _ => j) (hi z hz) (hj z hz)
    rw [gs_mul _ z _ hz]
    erw [e1, e1', e2, e2', e3, e4, e5, e6, e7]
  · exact LinearEquiv.apply_symm_apply _ _

theorem secPull_secOfTwist_eq {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec)
    (b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤))
    (hb : ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    (a : Γ(twist (QCoh.structureModule X) M, ⊤)) (ha : (Twist.map M (toSubscheme I)).app ⊤ a = b) :
    GlobalTheory.secPull (Twist.secOfTwist (𝟙 _) a) I.subschemeι = σ := by
  refine DVR.SecOps.sec_ext fun J => ?_
  have h1 := hb (J PUnit.unit)
  rw [← ha, coord_map_app] at h1
  change (I.subschemeι.appLE _ _ _).hom (resG X _ (structureModuleSectionsEquiv _ (coord a (J PUnit.unit)))) = _

  set i := J PUnit.unit
  have hJ : (fun _ : PUnit => i) = J := rfl
  have h2 : (I.subschemeι.app (⊤ ⊓ M.U i)).hom (structureModuleSectionsEquiv _ (coord a i)) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f J) := h1
  have e3 : ∀ y : Γ(X, ⊤ ⊓ M.U i), (I.subschemeι.appLE (M.U i) ((M.pull I.subschemeι).U J)
      (fun z hz => (mem_pull (F := I.subschemeι)).1 hz)).hom (resG X (le_inf le_top le_rfl) y) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => ⟨trivial, (mem_pull (F := I.subschemeι)).1 hz⟩ :
        (M.pull I.subschemeι).U J ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).op).hom ((I.subschemeι.app _).hom y) := by
    intro y
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  refine (e3 _).trans ?_
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun q => (I.subscheme.presheaf.map q).hom (σ.f J)) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_secPull_eq_of_subsingleton {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (hM : M.IsLB)
    (h : Subsingleton (coh (twist (idealModule I) M) 1)) (σ : (M.pull I.subschemeι).Sec) :
    ∃ s : M.Sec, GlobalTheory.secPull s I.subschemeι = σ := by
  haveI := epi_toSubscheme I
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (idealModuleι I) (toSubscheme I) (Limits.kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hsurj := cohOn.app_surjective (Twist.shortExact_map hM hS) ⊤ h
  obtain ⟨b, hb⟩ := exists_twistSec_of_sec I M σ
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨_, secPull_secOfTwist_eq I M σ b hb a ha⟩

theorem eventually_exists_secPull_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  intro X _ _ p hp N Z hN
  letI := algebraΓOfHom p
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  refine (hN.eventually_subsingleton_coh_twist (f := p) (fun _ => rfl)
    (idealModule (Scheme.IdealSheafData.vanishingIdeal Z))).mono fun l hl σ => ?_
  exact exists_secPull_eq_of_subsingleton _ _ (isLB_lbPow hN.isLB l) (hl 1 one_pos) σ

end GlobalTheory.LiftClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ZarGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_pull {T Y : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' t => ?_⟩
  rw [evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

omit [GrpObj A] in

theorem hom_open_eq (V : S.Opens) {Y : Over S} (u u' : Y ⟶ Over.mk V.ι) : u = u' := by
  apply Over.OverMorphism.ext
  have h : u.left ≫ V.ι = u'.left ≫ V.ι := (Over.w u).trans (Over.w u').symm
  exact (cancel_mono V.ι).1 h

omit [GrpObj A] in

theorem exists_hom_open (V : S.Opens) (Y : Over S) (h : ∀ z, Y.hom z ∈ V) : Nonempty (Y ⟶ Over.mk V.ι) := by
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _)⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h z

theorem isChart_of_rep (V : S.Opens) {B : Over S} (b : B ⟶ Over.mk V.ι) {P : LB (A ⊗ B).left} (h : Rep A b P) :
    IsChart A P where
  fam := h.fam
  inj := by
    intro Y u u' hs
    have hA : (ev P (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.fam.isLB _
    have hB : (ev P (fst A Y) (snd A Y ≫ u')).IsLB := pull_isLB h.fam.isLB _
    obtain ⟨x, -, hx⟩ := h.univ Y (u ≫ b) _ (fam_pull h.fam u)
    rw [hx u ⟨rfl, LBIso.trans hA hB hA hs (LBIso.symm hs)⟩, hx u' ⟨hom_open_eq V _ _, hs⟩]
  chart := by
    intro T N hN
    refine ⟨T.hom ⁻¹ᵁ V, fun Y y => ⟨?_, ?_⟩⟩
    · rintro ⟨u, -⟩ z
      have hb : b.left ≫ V.ι = B.hom := Over.w b
      have e : (u.left ≫ b.left) ≫ V.ι = y.left ≫ T.hom := by
        rw [Over.w y, Category.assoc, hb, Over.w u]
      have hmem : (y.left ≫ T.hom) z ∈ Set.range V.ι := ⟨(u.left ≫ b.left) z, by rw [← e]; rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    · intro hz
      have hY : ∀ z, Y.hom z ∈ V := fun z => by
        rw [← Over.w y]
        exact hz z
      obtain ⟨t⟩ := exists_hom_open V Y hY
      obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ Y t _ (fam_pull hN y)
      exact ⟨x, hx⟩

omit [GrpObj A] in

theorem good_iso_comp {g : ℕ} {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y}
    (h : GlobalTheory.DualCon.Good g f) : GlobalTheory.DualCon.Good g (e ≫ f) := ⟨MorphismProperty.RespectsIso.precomp @IsProper e f h.proper,
  by
    haveI := h.smooth
    have h0 : SmoothOfRelativeDimension (0 + g) (e ≫ f) := inferInstance
    rwa [zero_add] at h0,
  by
    haveI := h.conn
    have hsq : IsPullback e (e ≫ f) f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h.conn⟩

theorem zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  intro S A _ hA Ix V g hcov hrep
  have hrep' : ∀ i, ∃ (B : Over S) (b : B ⟶ Over.mk (V i).ι) (P : LB (A ⊗ B).left),
      Rep A b P ∧ GlobalTheory.DualCon.Good (g i) b.left := hrep
  choose Bi bi Pi hRi hGi using hrep'
  obtain ⟨B, P, j, hR, -, -, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing S A hA Ix Bi Pi
    (fun i => isChart_of_rep (V i) (bi i) (hRi i)) (by
      intro K _ _ s N hN
      obtain ⟨i, hi⟩ := hcov (s (default : Sp K))
      have hs : ∀ z : Sp K, s z ∈ V i := fun z => by
        rw [Subsingleton.elim z default]
        exact hi
      obtain ⟨t⟩ := exists_hom_open (V i) (Over.mk s) hs
      obtain ⟨x, ⟨-, hx⟩, -⟩ := (hRi i).univ _ t N hN
      exact ⟨i, x, (same_id_iff hN.isLB (hRi i).fam.isLB x).2 hx⟩)
  refine ⟨B, P, hR, fun i => ?_⟩
  have hpb : IsPullback (fst B (Over.mk (V i).ι)) (snd B (Over.mk (V i).ι)) (toUnit B)
      (toUnit (Over.mk (V i).ι)) :=
    IsPullback.of_is_product' (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      SemiCartesianMonoidalCategory.isTerminalTensorUnit
  have hR' := GlobalTheory.T.rep_ev_of_isPullback S A B (𝟙_ (Over S)) (Over.mk (V i).ι) (B ⊗ Over.mk (V i).ι) (toUnit B) P
    (toUnit _) (fst _ _) (snd _ _) hR hpb
  obtain ⟨e, he, -⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso S A _ _ _ (snd B (Over.mk (V i).ι)) _ (bi i) (Pi i) hR' (hRi i)
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have h2 := good_iso_comp e.hom.left (hGi i)
  rw [← Over.comp_left, he] at h2
  exact h2

end GlobalTheory.DualCon.ZarGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def pullCompare {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    {D : Type} [CommRing D] [Algebra R D] (w : Pt Y D) (z : Pt X D) (h : z = w ≫ u) :
    trivAt z ⟶ m.obj (trivAt w) :=
  Thick.trivHom { RingHom.id D with commutes' := fun _ ↦ rfl } (by
    change spMap (RingHom.id D) ≫ z.left = w.left ≫ u.left
    rw [Cris.spMap_id, h]; simp)

theorem exists_crystallineCocycleOnPoints_pullback_cohomologous {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    ∃ c : Fn0 Y, ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (w : Pt Y D),
      fv (m.coef.pullbackOneCocycle f) D D' φ w = fv f D D' φ (w ≫ u) + (c D' (spOver φ ≫ w) - φ (c D w)) := by
  refine ⟨fun D _ _ w ↦ ev f (pullCompare u m w (w ≫ u) rfl), fun D _ _ D' _ _ φ w ↦ ?_⟩
  have h1 : ∀ (z : Pt X D') (h : z = (spOver φ ≫ w) ≫ u),
      @Eq D' (ev f (pullCompare u m (spOver φ ≫ w) z h))
        (ev f (pullCompare u m (spOver φ ≫ w) _ rfl)) := fun z h ↦ by subst h; rfl
  have k := ev_sq f (trivMap φ (w ≫ u))
    (pullCompare u m (spOver φ ≫ w) (spOver φ ≫ w ≫ u) (Category.assoc _ _ _).symm)
    (pullCompare u m w (w ≫ u) rfl) (m.functor.map (trivMap φ w)) fun _ ↦ rfl
  have key : ∀ a b b' c d : D', b = b' → a + b = c + d → d = a + (b' - c) :=
    fun a b b' c d e h ↦ by rw [← e]; linear_combination -h
  exact key _ _ _ _ _ (h1 _ _) k

theorem exists_isAdd_of_mem_primDR (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hf : CatCoh.H1.mk _ f ∈ primDR A) :
    ∃ g : Fn2 A, IsAdd (fv f) g := by
  have h := (mem_prim_iff (dp0 R) (𝟙 _) A _).1 hf
  have M : ∀ u : A ⊗ A ⟶ A,
      IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 _) (RingHom.id R) u.left := fun u ↦
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have h' : CatCoh.H1.mk _ ((M μ[A]).coef.pullbackOneCocycle f) =
      CatCoh.H1.mk _ ((M (fst A A)).coef.pullbackOneCocycle f + (M (snd A A)).coef.pullbackOneCocycle f) := by
    rw [map_add]; exact h
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 h'
  obtain ⟨c, hc⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M μ[A]) f
  obtain ⟨c₁, hc₁⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (fst A A)) f
  obtain ⟨c₂, hc₂⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (snd A A)) f
  let k' : Fn0 (A ⊗ A) := fun D _ _ w ↦ k (trivAt w)
  refine ⟨fun D _ _ x y ↦ k' D (lift x y) - c D (lift x y) + c₁ D (lift x y) + c₂ D (lift x y),
    fun D _ _ D' _ _ φ x y ↦ ?_⟩
  have e : k' D' (spOver φ ≫ lift x y) - φ (k' D (lift x y)) =
      fv ((M μ[A]).coef.pullbackOneCocycle f) D D' φ (lift x y) -
        (fv ((M (fst A A)).coef.pullbackOneCocycle f) D D' φ (lift x y) +
          fv ((M (snd A A)).coef.pullbackOneCocycle f) D D' φ (lift x y)) :=
    congrFun (congrFun (congrFun hk _) _) (trivMap φ (lift x y))
  rw [hc, hc₁, hc₂, lift_fst, lift_snd, ← Hom.mul_def, comp_lift] at e
  simp only [map_add, map_sub]
  linear_combination e

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartLiftToModuliScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points

namespace GlobalTheory.Poinc.ChartAt

theorem exists_affine_chart_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ w hw
  haveI := X₁.imm
  set V : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ i.opensRange with hVdef
  have hwV : w ∈ V := by
    show X₁.π w ∈ (i.opensRange : Set Z)
    simpa [Scheme.Hom.coe_opensRange] using hw
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X₁.M.Z) (U := V) hwV
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hUi : ∀ w' ∈ U, X₁.π w' ∈ Set.range i := by
    intro w' hw'
    have := hUV hw'
    simpa [hVdef, Scheme.Hom.coe_opensRange] using this
  let φ : Γ(X₁.M.Z, U) ⟶ CommRingCat.of (X₁.M.ringOn U) :=
    CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom
  let f : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z := Spec.map φ ≫ hU.fromSpec
  have hrange : Set.range (f ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    apply hUi
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  refine ⟨U, IsOpenImmersion.lift i (f ≫ X₁.π) hrange, hU, hwU, hUi, ?_⟩
  rw [← cancel_mono i, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, ← X₁.comp]
  have hpt : ⊤ ≤ X₁.M.pt ⁻¹ᵁ U := X₁.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (X₁.M.ringOn U).val.toRingHom = valMap X₁.M.pt U hpt := by
    ext a
    show ((X₁.M.sectionsEquiv U hne a : X₁.M.ringOn U) : X₁.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (X₁.M.ringOn U).val.toRingHom ≫ f = X₁.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [f, Category.assoc]

end GlobalTheory.Poinc.ChartAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializations
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.BadOpen

theorem exists_affine_nhds_avoid : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  intro X Y _ s _ T σ y N hT hbad
  obtain ⟨g, hg⟩ := N.exists_isEqn y
  obtain ⟨U₁, hyU₁, hU₁⟩ := hg.exists_nhds
  set C : Set X := ⋃ v ∈ T, s.base '' (closure {v} ∩ closure {σ}) with hC
  have hCc : IsClosed C := by
    refine hT.isClosed_biUnion fun v _ => ?_
    exact s.isClosedMap _ (isClosed_closure.inter isClosed_closure)
  have hyC : y ∉ C := by
    simp only [hC, Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro v hv w hw hwy
    exact hbad v hv w (specializes_iff_mem_closure.2 hw.1) (specializes_iff_mem_closure.2 hw.2)
      (hwy ▸ specializes_rfl)
  let V : X.Opens := U₁ ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := y) ⟨hyU₁, hyC⟩
  refine ⟨W, g, hW, hyW, fun x hx => hU₁ x (hWV hx).1, fun v hv w hvw hσw hw => ?_⟩
  have := (hWV hw).2
  apply this
  simp only [hC, Set.mem_iUnion, Set.mem_image]
  exact ⟨v, hv, w, ⟨specializes_iff_mem_closure.1 hvw, specializes_iff_mem_closure.1 hσw⟩, rfl⟩

end GlobalTheory.BadOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusUnitClosedFibreSemiAbStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_unit_closedFibre_semiAb : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  first | exact @GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | exact GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit | (intros; apply GlobalTheory.SemiAbAffineUnit.exists_affine_nonzeroLocus_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimageStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i → IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O → ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  first | exact @GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | exact GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | (intros; apply GlobalTheory.Pinch.exists_affine_basicOpen_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleDivSymm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SymDiv

theorem exists_ampleDiv_symm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → ∃ D : CartierDiv A.left, AmpleDiv D ∧ LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) := by
  intro R _ A _ _ hA L hL hamp
  classical
  have hprop : IsProper A.hom := hA.proper
  set σ := (GrpObj.inv : A ⟶ A).left with hσ
  have hii : (GrpObj.inv : A ⟶ A) ≫ (GrpObj.inv : A ⟶ A) = 𝟙 A := by
    have h := IsIso.hom_inv_id (GrpObj.inv : A ⟶ A)
    rwa [GrpObj.inv_inv] at h
  have hii' : σ ≫ σ = 𝟙 A.left := by
    rw [hσ, ← Over.comp_left, hii, Over.id_left]
  have : IsIso σ := ⟨⟨σ, hii', hii'⟩⟩
  set L' := LB.LinComb L (K := Fin 2) ![𝟙 A.left, σ] ![1, 1] with hL'def
  have hL' : L'.IsLB := LB.isLB_linComb hL (K := Fin 2) ![𝟙 A.left, σ] ![1, 1]
  have hamL : IsAmpleLB L := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  have hamσ : IsAmpleLB (L.pull σ) := hamL.pull_of_isAffineHom σ
  have hamL' : IsAmpleLB L' := by
    refine hamL.tensor hamσ hL' ?_
    have hM := pull_isLB hL σ
    have hD1 := LB.isLB_div hL' hL
    have hD2 := LB.isLB_div hD1 hM
    refine (CechPic.cls_eq_zero_iff hD2).1 ?_
    rw [CechPic.cls_div hD1 hM, CechPic.cls_div hL' hL, CechPic.cls_linComb hL _ _ hL', CechPic.cls_pull hL σ hM]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_zsmul,
      CechPic.pull_id]
    abel
  have : CompactSpace A.left := hamL'.compactSpace
  obtain ⟨i₀, h₀⟩ := exists_chart hL' (genericPoint A.left)
  refine ⟨ofLB hL' i₀ h₀, ?_, ?_⟩
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    exact (ampleDiv_iff_isAmpleLB _ _).2 (hamL'.of_lbIso hT e.symm)
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    have hs : LBIso (L'.pull σ) L' := GlobalTheory.SymLB.pull_inv_symm_iso _ A L hL
    have e₁ : LBIso ((toLB (ofLB hL' i₀ h₀)).pull σ) (L'.pull σ) := GlobalTheory.FamRep.lbIso_pull e.symm σ
    exact LBIso.trans (pull_isLB hT σ) hL' hT (LBIso.trans (pull_isLB hT σ) (pull_isLB hL' σ) hL' e₁ hs) e

end GlobalTheory.SymDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left), IsAmpleLB M₀ → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_isAmpleLB_symm | exact GlobalTheory.SymAmple.exists_isAmpleLB_symm | (intros; apply GlobalTheory.SymAmple.exists_isAmpleLB_symm <;> assumption)
end

