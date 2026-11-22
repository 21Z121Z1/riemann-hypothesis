import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0045
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.NeutralLevel

theorem isGrpPullback_of_iso_inv {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (e : (Over.pullback f).obj G ≅ G') (he : IsMonHom e.hom) :
    IsGrpPullback G' G f (e.inv.left ≫ pullback.fst G.hom f) :=
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G f)).congr (Category.id_comp _) rfl

theorem exists_extension {S S' T : Scheme.{0}} {f : S' ⟶ S} {j : T ⟶ S'} {G : Over S} {G' : Over S'} {A : Over T}
    [GrpObj G] [GrpObj G'] [GrpObj A] {φ : G'.left ⟶ G.left} {ψ : A.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (hA : IsGrpPullback A G' j ψ) (c : ℕ)
    (hc : ∀ a : 𝟙_ (Over T) ⟶ A, ∃ s : 𝟙_ (Over S') ⟶ G', j ≫ s.left = (a ^ c).left ≫ ψ)
    (t : T ⟶ S) (ht : t = j ≫ f) (y : Over.mk t ⟶ G) :
    ∃ s : S' ⟶ G.left, s ≫ G.hom = f ∧ j ≫ s = (y ^ c).left := by
  have H := hA.comp h
  obtain rfl : t = (𝟙_ (Over T)).hom ≫ j ≫ f := ht.trans (Category.id_comp _).symm
  let a : 𝟙_ (Over T) ⟶ A := Over.homMk (H.1.lift y.left (𝟙_ (Over T)).hom (Over.w y)) (H.1.lift_snd _ _ _)
  have ha : pushHom H _ a = y := Over.OverMorphism.ext (H.1.lift_fst _ _ _)
  obtain ⟨s, hs⟩ := hc a
  refine ⟨s.left ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, h.1.w, ← Category.assoc, Over.w s]
    exact Category.id_comp _
  · rw [← ha, ← map_pow, ← Category.assoc]
    exact (congrArg (· ≫ φ) hs).trans (Category.assoc _ _ _)

theorem exists_ampleCub_fibre {S S' T : Scheme.{0}} {f : S' ⟶ S} (j : T ⟶ S') {G : Over S} {G' : Over S'}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
    (L : LB ((Over.pullback j).obj G').left) (hL : AmpleCub ((Over.pullback j).obj G') L)
    (t : T ⟶ S) (ht : j ≫ f = t) :
    ∃ N : LB ((Over.pullback t).obj G).left, AmpleCub ((Over.pullback t).obj G) N := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G t)
    (((isGrpPullback_pullback G' j).comp h).congr ht rfl)
  exact GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso _ _ _ e he L hL

theorem smoothOfRelativeDimension_model {K W : Type} [Field K] [CommRing W] [IsDomain W]
    [Algebra K (FractionRing W)] (P : Out.PolAV (Sp K)) (G : Over (Sp W)) [GrpObj G] (hG : SmConn G)
    (hm : IsModel (L := FractionRing W) P.A G) : SmoothOfRelativeDimension P.g G.hom := by
  obtain ⟨e, -⟩ := hm
  obtain ⟨-, _, -, -, _⟩ := hG
  refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic W G P.g ?_
  have w : e.hom.left ≫ _ = pullback.snd G.hom (Out.jK W) := Over.w e.hom
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩)
    (GlobalTheory.TorusModel.polPull (spMap (algebraMap K (FractionRing W))) P).smoothDim

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_level_model : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  intro V K _ _ _ _ _ _ R K' _ _ _ _ _ _ _ hR hc P
  have : IsFractionRing R K' := hR.2.2.2
  let P' := GlobalTheory.TorusModel.polPull (spMap (algebraMap K K')) P
  obtain ⟨G', _, hG', he, c, hc1, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K' hR P'.A P'.isAb
    (GlobalTheory.AbProj.isProjBy_of_isPullback P' (IsPullback.id_horiz _))
  obtain ⟨L', hL'⟩ := GlobalTheory.SS.exists_ampleCub_spFibre R K' hR P' G'.Y hG' G'.e he
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R K' hc P.A P.isAb G'.Y hG' ⟨G'.e, he⟩
  refine ⟨s, c, hc1, fun W hW hsW hl => ?_⟩
  obtain ⟨G, _, _, ε, hG, hε, hcomm, hm⟩ := hs W hW hsW hl
  have h := isGrpPullback_of_iso_inv _ G ε hε
  have hA := isGrpPullback_of_iso_inv _ G'.Y G'.e he
  exact ⟨G, inferInstance, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, hG, hcomm, hm,
    smoothOfRelativeDimension_model P G hG hm,
    exists_ampleCub_fibre _ h L' hL' _ (spMap_comp_spMap _ _),
    fun y => exists_extension h hA c hext _ (spMap_comp_spMap _ _).symm y⟩

end GlobalTheory.NeutralLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitTerm
open TWM TWO

theorem exists_torsion_isUnit (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) {I : Type} [Fintype I] {φ : I → ((Over.mk t ⊗ P.A).left ⟶ P.A.left)}
    {ε : I → ℤ} (σ : LB.Sec (LB.LinComb P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ P.A) (j : ℕ), x ^ l ^ j = 1 ∧
      ∀ z J, Good P.L z J → IsUnit (sval σ (lift (𝟙 (Over.mk t)) x).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hσ
  have hsm := P.isAb.smooth
  let p : (Over.mk t ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst (Over.mk t) P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst t P.A.hom))
  have : IsReduced (Over.mk t ⊗ P.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  obtain ⟨P', g, hg, -, hmul, -⟩ := hL.polBaseChange _ _ t P
  let e : P'.A.left ≅ (Over.mk t ⊗ P.A).left := hg.flip.isoPullback
  let W := (Over.mk t ⊗ P.A).left.basicOpen (σ.f j)
  have hW : (W : Set (Over.mk t ⊗ P.A).left).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
    hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  obtain ⟨y, hy⟩ := hW
  obtain ⟨_, hq, hq'⟩ := (PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred K P' l hl
    hK).inter_open_nonempty (e.hom ⁻¹ᵁ W) (e.hom ⁻¹ᵁ W).isOpen ⟨e.inv y, by
      show e.hom (e.inv y) ∈ W
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; exact hy⟩
  obtain ⟨x, ⟨m, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hq'
  let Φ : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ t) ⟶ P.A) :=
    MonoidHom.mk' (fun x => toBase hg.w x) (hmul _)
  let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  have er : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left = x.left ≫ e.hom := by
    refine pullback.hom_ext ?_ ?_
    · refine (congrArg (fun q => q.left) (lift_fst (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_fst).trans (Over.w x))).symm
    · refine (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk t)) (ρ ≫ Φ x))).trans ?_
      exact (Category.id_comp _).trans
        ((Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) hg.flip.isoPullback_hom_snd)).symm
  refine ⟨ρ ≫ Φ x, m, by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one], fun z J hJ => ?_⟩
  obtain rfl : z = q := H1.SquareUnits.spec_pt_eq z q
  have hz : (lift (𝟙 (Over.mk t)) (ρ ≫ Φ x)).left z ∈ W := by rw [er]; exact hq
  exact H1.SectionArithmetic.isUnit_sval σ _ z hJ j hz

theorem exists_sec_lin {Y : Scheme.{0}} {M : LB Y} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j :=
  ⟨⟨fun j => ∑ i, (SecOps.secScale (b i) (t i)).f j, fun i j => by
    simp only [map_sum, (SecOps.secScale _ _).compat, Finset.mul_sum]⟩, fun _ => rfl⟩

theorem exists_torsion_sum (hL : Laws) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} {m : ℕ}
    (b : Fin m → D.SecB k α) {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (hb : IsSecBasis (T := Over.mk t) (A := D.P.A) _
      (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left))
    (a : Fin m → K) (ha : ∃ i, a i ≠ 0) {l : ℕ} (hl : 2 ≤ l) (hK : (l : K) ≠ 0) :
    ∃ (x : Over.mk t ⟶ D.P.A) (j : ℕ), x ^ l ^ j = 1 ∧ ∀ (z : Spec (CommRingCat.of K)) J, Good D.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) * sval (Z := Spec (CommRingCat.of K)) (b i) x.left z J) := by
  obtain ⟨σ, hσ⟩ := exists_sec_lin
    (fun i => (fst (Over.mk t) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)))
    (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left)
  obtain ⟨x, j, hx, hu⟩ := exists_torsion_isUnit hL D.P t σ (fun h => by
    obtain ⟨i, hi⟩ := ha
    have e := (hb σ).unique (y₁ := fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) (y₂ := 0) hσ
      (fun j => (h j).trans (Finset.sum_eq_zero fun i _ => by
        rw [Pi.zero_apply, map_zero, map_zero, MulZeroClass.zero_mul]).symm)
    exact hi ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      ((congrFun e i).trans (map_zero _).symm))) hl hK
  refine ⟨x, j, hx, fun z J hJ => ?_⟩
  have q := hu z J hJ
  rw [SectionScalarValuation.sval_lin _ _ hσ _ z hJ] at q
  refine (congrArg IsUnit (Finset.sum_congr rfl fun i _ => ?_)).mp q
  rw [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, IntegralCoord.gs_appTop, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd]
  rfl

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem genV_torsion {N : ℕ} (hN : N ≠ 0) (g : GtPtF D.toPre F)
    (hg : letI := TorusExt.gtGroup D.toPre F; N • g = 0) (χ : D.toPre.X) : GenV hϖ hv (g.s χ) 0 := by
  letI := TorusExt.gtGroup D.toPre F
  choose l hl hu using fun g : GtPtF D.toPre F => CoefVal.exists_gtV (hϖ := hϖ) (hv := hv) g
  let L : GtPtF D.toPre F →+ (D.toPre.X →+ ℚ) := AddMonoidHom.mk' l fun g g' =>
    (hu (g + g') (l g + l g') (CoefVal.gtV_add ((TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hl g) (hl g'))).symm
  have e : N • l g = 0 := by
    show N • L g = 0
    rw [← map_nsmul, hg, map_zero]
  have e' : l g χ = 0 := by
    have := DFunLike.congr_fun e χ
    simpa [hN] using this
  rw [← e']
  exact hl g χ

theorem exists_value_unit {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α) (a : Fin m → Ov v)
    (x : TO hϖ hv ⟶ D.toPre.P.A)
    (hu : ∀ (z : Spec (CommRingCat.of (ResidueField (Ov v)))) J, Good D.toPre.P.L z J →
      IsUnit (∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField (Ov v)))).inv.hom (residue _ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left) z J)) :
    ∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)), G₀.IsGen ∧
      ∃ c : F, v c = 0 ∧ ∀ (z : (TF (R := V) F).left) J, Good D.toPre.P.L z J →
        ∑ i, GlobalTheory.UT.cst F z (a i) * sval (b i) (ιS hϖ hv ≫ x).left z J =
          GlobalTheory.UT.cst F z c * (val G₀ (ιS hϖ hv).left z J).val := by
  have hL := D.toPre.P.isLB
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local (V := Ov v) D.toPre.P.L hL
    (fun i => x.left ≫ DegPre.famφB D.toPre α i) (DegPre.famε k)
  choose y hy using fun i => TwistUnit.exists_ratio_local (R := Ov v) hL (H1.SectionArithmetic.pullSec (b i) x.left) G₀ hG₀
  have key : ∀ {E : Type} [CommRing E] (φ : Ov v →+* E) (z : Spec (CommRingCat.of E)) J, Good D.toPre.P.L z J →
      ∑ i, gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (φ (a i))) *
        sval (b i) (Spec.map (CommRingCat.ofHom φ) ≫ x.left) z J =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)))) *
        (val G₀ (Spec.map (CommRingCat.ofHom φ)) z J).val := fun φ z J hJ => by
    rw [map_sum, map_sum, SectionScalarValuation.gs_sum _ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial (y i)
    rw [Category.id_comp] at e
    have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap (CommRingCat.ofHom φ) (y i)))
    have q := (H1.SectionArithmetic.sval_pullSec (b i) x.left _ z hJ).symm.trans (hy i _ (Spec.map (CommRingCat.ofHom φ)) z J hJ)
    rw [map_mul, map_mul, gs_mul _ z ⊤ trivial, _root_.mul_assoc]
    exact congrArg (_ * ·) (q.trans (congrArg (· * _) e'))
  have hc : IsUnit (∑ i, a i * (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (y i)) := by
    let z₀ : Spec (CommRingCat.of (ResidueField (Ov v))) := closedPoint _
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z₀
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit (key (residue _) z₀ J hJ)).mp (hu z₀ J hJ))
    refine isUnit_of_map_unit (residue _) _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁
  exact ⟨G₀, hG₀, _, v_unit v hc.unit, fun z J hJ => key (algebraMap (Ov v) F) z J hJ⟩

theorem exists_coord {k : ℕ} {α : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k α)
    (hb : IsSecBasis (T := TO hϖ hv) (A := D.toPre.P.A) _ (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α)
      (DegPre.famε k) (b i) (snd (TO hϖ hv) D.toPre.P.A).left))
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} (hs : VGe D F v k α s 0) :
    ∃ a : Fin m → Ov v, (∀ q : ℚ, (∀ i, (q : WithTop ℚ) ≤ v (a i)) → VGe D F v k α s q) ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (a i)) * sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, c, σ, σF, hσ, hc, hsum⟩ := hs
  let c₀ : Fin n → Γ(Spec (CommRingCat.of (Ov v)), ⊤) := fun l =>
    (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom ⟨c l, hc l⟩
  have ec : ∀ l, ιr (v := v) (c₀ l) = c l := fun l =>
    congrArg (algebraMap (Ov v) F) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Ov v))) ⟨c l, hc l⟩)
  obtain ⟨t, ht⟩ := exists_sec_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (c₀ l))
    (fun l => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (σ l) (snd (TO hϖ hv) D.toPre.P.A).left)
  obtain ⟨r, hr, -⟩ := hb t
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = ∑ i, gs ρ z ⊤ (gF D.toPre F (ιr (v := v) (r i))) *
        sval (b i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    have e₁ := SectionScalarValuation.sval_lin _ _ ht (ρ ≫ (jO hϖ hv).left) z hJ
    have e₂ := SectionScalarValuation.sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) _ hr
      (ρ ≫ (jO hϖ hv).left) z hJ
    simp only [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ, gs_jO, ec, Category.assoc, jO_snd] at e₁ e₂
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) σF (fun j => hsum j) ρ z hJ, ← e₂, e₁]
    exact Finset.sum_congr rfl fun l _ => by rw [SectionScalarValuation.secScal_sval (hσ l) ρ z hJ]
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom (r i), fun q hq => ?_, key⟩
  have hF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  choose bF hbF using fun i => exists_sec hL hF (pullSec D.toPre.P.L _ _ (b i) (DegPre.prB D.toPre F).left)
  have hb' := fun i y J hJ => (hbF i _ (𝟙 _) y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)
  refine ⟨m, _, b, bF, fun i => SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hb' i y J hJ).symm, hq,
    IntegralCoord.lin_of_sval hL (fun i => gF D.toPre F (ιr (v := v) (r i))) bF fun y J hJ => ?_⟩
  rw [key _ _ y J hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (_ * ·) (hb' i y J hJ).symm

end

theorem exists_eq_zero {n : ℕ} (c : Fin n → WithTop ℚ) (h₀ : ∀ i, 0 ≤ c i)
    (h : ∀ q : ℚ, 0 < q → ¬ ∀ i, (q : WithTop ℚ) ≤ c i) : ∃ i, c i = 0 := by
  by_contra hc
  have h₁ : (0 : WithTop ℚ) < Finset.univ.inf c := (Finset.lt_inf_iff (WithTop.coe_lt_top 0)).2 fun i _ =>
    lt_of_le_of_ne (h₀ i) fun e => hc ⟨i, e.symm⟩
  obtain ⟨q, hq, hq'⟩ := WithTop.lt_iff_exists_coe_btwn.1 h₁
  exact h q (WithTop.coe_lt_coe.1 hq) fun i => hq'.le.trans (Finset.inf_le (Finset.mem_univ i))

theorem exists_torsion_coef_val_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k n hk hn hnV s α hs hs'
  have hM := D.toPre.P.isLB
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  obtain ⟨m, b, -, hb⟩ := hT V D.toPre k (by omega) α
  have hb₁ : ∀ (R' : Type) [CommRing R'] (f : V →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of V)),
      t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T := Over.mk t) (A := D.toPre.P.A) _
        (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.toPre.P.A).left) := by
    intro R' _ f t ht
    subst ht
    exact hb R' f _ (fun i j => rfl)
  obtain ⟨a, ha, hsa⟩ := exists_coord hϖ hv b (hb₁ _ _ _ rfl) hs
  obtain ⟨i₀, hi₀⟩ := exists_eq_zero (fun i => v (a i)) (fun i => (a i).2) fun q hq h => hs' q hq (ha q h)
  have hres : residue (Ov v) (a i₀) ≠ 0 := by
    rw [residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
    exact (valuation_eq_one_iff (fun _ => Iff.rfl) _).2 hi₀
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, j, hx₀, hu⟩ := exists_torsion_sum hL.1 D.toPre b
    (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom)
    (hb₁ _ ((residue (Ov v)).comp (fO v hϖ hv)) _ (Spec.map_comp _ _).symm) (fun i => residue _ (a i)) ⟨i₀, hres⟩
    hn.two_le hK
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P (n ^ j) (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n ^ j = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    ExactTerm.exists_torsion_lift (Ov v) D.toPre.P.A (n ^ j) (TO hϖ hv).hom x₀ hx₀
  obtain ⟨G₀, hG₀, c, hc, hval⟩ := exists_value_unit hϖ hv b a x (fun z J hJ => by rw [ex]; exact hu z J hJ)
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨g, hg₁, hg₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq hN (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨j, g, 0, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hg₂.symm, fun w _ hω => ?_⟩
  obtain ⟨d, hd, vd⟩ := CoefUnit.v_of_isCoef hϖ hv (genV_torsion hϖ hv hN g hg₂ α) hω x hg₁.symm (s.s α) G₀ hG₀ c
    (fun z J hJ => by
      rw [hsa _ _ z J hJ, ← hval z J hJ, ← Over.comp_left, lift_snd, hg₁]
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl)
  rw [CoefBasic.coef_eq hd, vd, hc]
  simp

end GlobalTheory.OneBasis.UnitTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesProd

theorem hasSum_of_sumI {R F Ix : Type} [CommRing R] [NormedField F] (φ : R →+* F)
    (h1 : ∀ a, ‖φ a‖ ≤ 1) (I : Ideal R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ϖ : R) (hI : I = Ideal.span {ϖ})
    (hϖ : ‖φ ϖ‖ ≤ r) [Module R F] (hs : ∀ (a : R) (x : F), a • x = φ a * x) {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumI I x s) : HasSum x s := by
  obtain ⟨N, hN, -, -, h⟩ := h
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ N, ‖y‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hN
    refine ⟨∑ t ∈ T, ‖t‖, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hs, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  have hb : ∀ (n : ℕ) y, y ∈ I ^ n • N → ‖y‖ ≤ r ^ n * C := by
    intro n y hy
    rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hs, norm_mul, map_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hϖ n) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 n)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hb n _ (hS T hT)).trans_lt hn

theorem hasSum_conv {F X : Type} [NormedField F] [IsUltrametricDist F] [AddCommGroup X] {a b c : X → F} {x y : F}
    (ha : HasSum a x) (hb : HasSum b y) (hc : ∀ α, HasSum (fun χ => a χ * b (α - χ)) (c α)) :
    HasSum c (x * y) := by
  have : NonarchimedeanRing F :=
    { is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup (M := F)).is_nonarchimedean }
  let e : X × X ≃ X × X :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  exact ((e.hasSum_iff.2 (ha.mul_of_nonarchimedean hb))).prod_fiberwise hc

open GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem mul_back {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k k' : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    (hL₂ : L₂.IsLB) (n : Z₁ ⟶ Y') (hn : n ≫ h₁ = 𝟙 _) {a a' a'' b b' b''}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k' g₁ h₁ a' (m ≫ f₂) (𝟙 _) b')
    (h'' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m (k + k') g₁ h₁ a'' (m ≫ f₂) (𝟙 _) b'')
    (hb : ∀ j, (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b''.f j) =
      (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b.f j) *
        (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b'.f j))
    (y : Z₁) (i : L₁.ι) (hi : g₁ y ∈ L₁.U i) :
    powVal a'' (𝟙 _) y i = powVal a (𝟙 _) y i * powVal a' (𝟙 _) y i := by
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← h.1, ← Category.assoc, hn, Category.id_comp]
  obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
  have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
  have v := (isoRelM_iff w m k h₁ h.1 _ h.2.1 a b).1 h _ n y i₂ i a₂ a₁
  have v' := (isoRelM_iff w m k' h₁ h.1 _ h.2.1 a' b').1 h' _ n y i₂ i a₂ a₁
  have v'' := (isoRelM_iff w m (k + k') h₁ h.1 _ h.2.1 a'' b'').1 h'' _ n y i₂ i a₂ a₁
  have e : powVal b'' (n ≫ 𝟙 _) y i₂ = powVal b (n ≫ 𝟙 _) y i₂ * powVal b' (n ≫ 𝟙 _) y i₂ := by
    rw [Category.comp_id]
    exact (congrArg (gs n y _) (hb fun _ => i₂)).trans (gs_mul n y _ (mem_wchart.2 fun _ => a₂) _ _)
  rw [v, v', v'', hn, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, _root_.mul_mul_mul_comm,
    ← Units.val_mul] at e
  exact (Units.mul_right_inj _).1 e

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_frm_mul {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} {w' : Frm D F k' b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ w'' : Frm D F (k + k') b, w''.IsGen ∧
      ∀ z J, Good D.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J := by
  obtain ⟨w'', h, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k + k'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [CoefBasic.prod_line, CoefBasic.prod_line, CoefBasic.prod_line, pow_add, pow_add, mul_inv,
        _root_.mul_mul_mul_comm])
    (LB.mulGen D.P.L _ _ _ _ w w') (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw')
  exact ⟨w'', h, fun z J hJ => (hv _ _ z J hJ).trans (val_mul hJ _ _ _)⟩

theorem exists_back {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {w : W0 U} (hw : w.IsGen) {k k' : ℕ}
    {σ : U.SecGF F k} {σ' : U.SecGF F k'} {σ'' : U.SecGF F (k + k')} {s s' s''}
    (h : U.ExpandsG F k σ s) (h' : U.ExpandsG F k' σ' s') (h'' : U.ExpandsG F (k + k') σ'' s'')
    (hb : ∀ j, (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j)
        from σ''.f j) =
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ.f j) *
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ'.f j)) :
    ∃ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F (k + k')), U.ExpandsF F k w t s ∧ U.ExpandsF F k' w t' s' ∧
      U.ExpandsF F (k + k') w t'' s'' ∧
      ∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have i₂ := fun k => (isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
  obtain ⟨t, ht⟩ := (i₂ k σ).exists
  obtain ⟨t', ht'⟩ := (i₂ k' σ').exists
  obtain ⟨t'', ht''⟩ := (i₂ (k + k') σ'').exists
  exact ⟨t, t', t'', ⟨σ, ht, h⟩, ⟨σ', ht', h'⟩, ⟨σ'', ht'', h''⟩, fun z J hJ =>
    mul_back U.LG.isLB n.left (congrArg (fun q => q.left) hn) ht ht' ht'' hb z _ (hJ (𝟙 _ ≫ _))⟩

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k k' g w w' w'' hk hk' hw hw' hw''
  obtain ⟨w₃, hw₃, hv⟩ := exists_frm_mul hw hw'
  obtain ⟨c, hc, -, hcoef⟩ :=
    ((CoefBasic.coef_basic _ u.D.toPre (PadicAlgCl p) (k + k') g).2.2 w₃ hw₃).2.2.1 w'' hw''
  refine ⟨c, hc, fun σ σ' σ'' s s' s'' h h' h'' hb x x' hx hx' => ?_⟩
  obtain ⟨w₀, hw₀⟩ := u.U.ext
  obtain ⟨t, t', t'', e, e', e'', hm⟩ := exists_back u.U.toUnifPre (PadicAlgCl p) hw₀ h h' h'' hb
  let φ : u.V →+* PadicAlgCl p :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))
  have : CharZero u.V := φ.charZero
  have hadm : AdmBase u.V (IsLocalRing.maximalIdeal u.V) :=
    ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hS := GlobalTheory.T.product_of_sections_expands_to_convolution hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) w₀ hw₀ k k' (k + k') hk hk' rfl
    t t' t'' s s' s'' e e' e'' hm g w w' w₃ hw hw' hw₃ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have h1 : ∀ a, ‖φ a‖ ≤ 1 := fun a => (u.norm_le _).2 ⟨a, rfl⟩
  have hlt : ‖φ ϖ‖ < 1 := lt_of_le_of_ne (h1 ϖ) fun e1 => by
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) ϖ)⁻¹).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) e1).le.trans inv_one.le)
    have h0 : algebraMap u.V (FractionRing u.V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  have hsum := hasSum_conv hx hx' fun α =>
    letI : Module u.V (PadicAlgCl p) := Module.compHom _ (algebraMap u.V (FractionRing u.V))
    hasSum_of_sumI φ h1 _ (norm_nonneg _) hlt ϖ hϖ.maximalIdeal_eq le_rfl
      (fun a x => Algebra.smul_def (algebraMap u.V (FractionRing u.V) a) x) (hS α)
  simp only [hcoef, _root_.mul_assoc]
  exact hsum.mul_left c

end GlobalTheory.ZH.SeriesProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelSeries_eq_unit_mul_thetaPoint : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  first | exact @GlobalTheory.ModelTheta.series_eq_unit_mul_theta | exact GlobalTheory.ModelTheta.series_eq_unit_mul_theta | (intros; apply GlobalTheory.ModelTheta.series_eq_unit_mul_theta <;> assumption)
end

