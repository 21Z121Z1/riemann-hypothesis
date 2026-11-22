import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.StrictPull

theorem exists_isPullDeg_of_strict (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens) (hW : Nonempty (PsiOn D W))
    (hη : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W)
    (P' : PolAV (Spec (CommRingCat.of R'))) (F : P'.A.left ⟶ D.P.A.left)
    (gp : IsGrpPullback P'.A D.P.A (specOf φ) F) (w : LB.Iso P'.L (D.P.L.pull F)) (hw : w.IsGen) (hs : Strict w) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = P'.g ∧ Strict hD.w := by
  obtain ⟨ψW⟩ := hW
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) (specOf φ) (fun _ => hE) D.rig D.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D.P.isLB P'.isLB hw' D.sym D.sym_gen D.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D.X → (𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ P'.A), ∀ x,
      (c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ (D.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (specOf φ ≫ (D.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ specOf φ))).left = specOf φ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D.c a) (toUnit _ ≫ D.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D.c_add]
    exact m
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = jK R' ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W.ι (jK R' ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R' y = genericPoint (Spec (CommRingCat.of R')) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R' (FractionRing R')) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
      show specOf φ (jK R' y) ∈ W
      rw [hy]; exact hη), IsOpenImmersion.lift_fac _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c x).left =
      ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := fun x => by
    show g ≫ W.ι ≫ (D.c x).left = (jK R' ≫ (c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi x) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen x) g)
  choose psi hpsi vpsi using fun x => exists_down_val hw' D.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  let D' : DegPre R' :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  refine ⟨D',
    ⟨e, e_hom, w, hw, hE, ?_, AddEquiv.refl _, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, hs⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ rig D.rig (specOf φ) _
      (rigPull_le (G' := P'.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 Hrig
  · refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

def polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem exists_isPullDeg_strict : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D W) → (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), D'.P.g = D.P.g ∧ Strict hD.w := by
  intro _ R R' _ _ _ _ φ D W hW hη
  obtain ⟨w, hw, hs⟩ := exists_strict D.P.isLB (pullback.fst D.P.A.hom (specOf φ))
  exact exists_isPullDeg_of_strict R R' φ D W hW hη (polPull D.P (specOf φ)) (pullback.fst D.P.A.hom (specOf φ))
    (isGrpPullback_pullback D.P.A (specOf φ)) w hw hs

end GlobalTheory.StrictPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace FiniteQuot

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

lemma translHom_eq (c : 𝟙_ (Over (Sp K)) ⟶ A) : (transl c).hom = (toUnit A ≫ c) * 𝟙 A := rfl

lemma comp_translHom {Z : Over (Sp K)} (g : Z ⟶ A) (c : 𝟙_ (Over (Sp K)) ⟶ A) :
    g ≫ (transl c).hom = (toUnit Z ≫ c) * g := by
  rw [translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

lemma translHom_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [translHom_eq, MonObj.comp_one, _root_.one_mul]

lemma translHom_mul (a c : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl (a * c)).hom = (transl a).hom ≫ (transl c).hom := by
  rw [comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc,
    _root_.mul_comm (toUnit A ≫ c)]

end FiniteQuot

open FiniteQuot PointQuot AbelianQuotient in

theorem exists_quotient_abelian_by_finite_points :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ C : Subgroup (𝟙_ (Over (Sp k)) ⟶ A), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A), x ≫ ψ = 1 ↔ ∃ c ∈ C, x = toUnit _ ≫ c := by
  intro k _ _ A _ hA C hC
  have := hA.comm
  have hq : IsQProjOver A.hom := by
    obtain ⟨N, i, hi, e⟩ := (ProjSpace.isProjBy_iff_isProjOver A.hom).1
      (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨Y, π, sY, hw, hG, hsep, hlft, -⟩ :=
    ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq
      (congrArg CommaMorphism.left (translHom_one (A := A)))
      (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1))
      (fun a => Over.w _) (by
        intro K _ _ y a h
        let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
        have h' : y' ≫ (transl a.1).hom = y' := Over.OverMorphism.ext h
        have : Nonempty (Over.mk (y ≫ A.hom)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
        have := epi_toUnit (Over.mk (y ≫ A.hom))
        rw [comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi] at h'
        exact Subtype.ext h')
  let B : Over (Sp k) := Over.mk sY
  let q : A ⟶ B := Over.homMk π hw
  have hfin : IsFinite q.left := hG.fin
  have het : Etale q.left := hG.etale
  have hsurj : Surjective q.left := hG.onto
  have hinv : ∀ c : C, (transl c.1).hom ≫ q = q := fun c => Over.OverMorphism.ext (hG.inv c)
  let x : C → (𝟙_ (Over (Sp k)) ⟶ A) := Subtype.val
  have hmono := mono_constDesc x Subtype.val_injective
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C Subtype.range_coe
  obtain ⟨_, hcomm, hhom, -⟩ := grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono
    inferInstance hsurj inferInstance (by
      intro Z g g'
      constructor
      · intro h
        obtain ⟨t, ht⟩ := exists_lift x (g' / g) fun z => by
          obtain ⟨V, a, hV, e⟩ :=
            hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z
          have e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g' := Over.OverMorphism.ext e
          refine ⟨V, hV, a, ?_⟩
          rw [GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]
        exact ⟨t, by rw [ht, div_mul_cancel]⟩
      · rintro ⟨t, rfl⟩
        refine hom_ext_local _ _ fun z => ?_
        obtain ⟨V, hV, c, hc⟩ := locally_const_desc x t z
        refine ⟨V, hV, ?_⟩
        rw [← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc,
          Category.assoc, hinv])
  refine ⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · have hw' : q.left ≫ B.hom = A.hom := Over.w q
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated B.hom := hsep
    have : LocallyOfFiniteType B.hom := hlft
    have : UniversallyClosed (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyReduced (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyConnected (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have := UniversallyClosed.of_comp_surjective q.left B.hom
    have := geometricallyReduced_of_comp q.left B.hom
    have : LocallyOfFinitePresentation B.hom := inferInstance
    exact ⟨hcomm, smooth_of_grpObj_of_flat B, ⟨⟩, geometricallyConnected_of_comp q.left B.hom⟩
  · have h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q := by rw [hy, MonObj.one_comp]
    obtain ⟨a, ha, -⟩ := hG.fibre K (1 : Over.mk t ⟶ A).left y.left
      (congrArg CommaMorphism.left h1)
    have ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y := Over.OverMorphism.ext ha
    exact ⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩,
      MonObj.one_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRealDimOneIsFractionRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RealInhabitant

open TorsionGenerators NumberField

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (a : ℤ) : unitOn (u ^ a) = unitOn u ^ a :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u a

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem map_unitOn {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (Geo.Tor.spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

theorem isPrimitiveRoot_map {B F : Type} [CommRing B] [IsDomain B] [Field F] (σ : B →+* F) {M : ℕ} (hM : (M : F) ≠ 0)
    {z : Bˣ} (hz : IsPrimitiveRoot z M) : IsPrimitiveRoot (Units.map σ.toMonoidHom z) M := by
  have : NeZero (M : F) := ⟨hM⟩
  have h₀ : 0 < M := Nat.pos_of_ne_zero fun e => hM (by rw [e, Nat.cast_zero])
  have h := ((IsPrimitiveRoot.coe_units_iff.2 hz).isRoot_cyclotomic h₀).map (f := σ)
  rw [Polynomial.map_cyclotomic] at h
  exact IsPrimitiveRoot.coe_units_iff.1 (Polynomial.isRoot_cyclotomic_iff.1 h)

theorem exists_finite_level (hL : Laws) {R₀ Q : Type} [CommRing R₀] [Field Q] [IsAlgClosed Q] (t : R₀ →+* Q)
    (P₀ : PolAV (Sp R₀)) {M : ℕ} (hM : (M : Q) ≠ 0) {ζ : Qˣ} (hζ : IsPrimitiveRoot ζ M) :
    ∃ s : Set Q, s.Finite ∧ ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (io : B →+* Q) (j : R₀ →+* B) (z : Bˣ),
      Function.Injective io → io.comp j = t → (∀ y ∈ s, y ∈ io.range) → Units.map io.toMonoidHom z = ζ →
      IsUnit (M : B) → ∀ (P : PolAV (Sp B)) (φ : P.A.left ⟶ P₀.A.left), IsPolFibre j P₀ P φ →
      Nonempty (Out.Level P M (unitOn z)) := by
  have := P₀.isAb.comm
  have := P₀.isAb.smooth
  have := P₀.isAb.proper
  obtain ⟨P', φ', β, h', -, hW⟩ := exists_fibre hL P₀ t
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL Q P' h'.1.symm M hM
    (unitOn ζ) (isPrimitiveRoot_unitOn hζ)
  choose s hs hb using fun i => exists_finite_coordinates P₀.A.hom t (β (x i)).left (Over.w _)
  refine ⟨⋃ i, s i, Set.finite_iUnion hs, fun B _ _ io j z hio hj hsB hzζ hMB P φ h => ?_⟩
  have := hio.isDomain io
  have : IsDominant (Geo.Tor.spMap io) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le)⟩
  choose b hb' using fun i => hb i B io hio (fun c => ⟨j c, congr($hj c)⟩)
    (fun y hy => hsB y (Set.mem_iUnion.2 ⟨i, hy⟩))
  have hs₀ : Geo.Tor.spMap io ≫ Geo.Tor.spMap j = Geo.Tor.spMap t := by rw [spMap_comp_spMap, hj]
  have hbw : ∀ i, b i ≫ P₀.A.hom = Geo.Tor.spMap j := fun i => ext_of_isDominant (Geo.Tor.spMap io) (by
    rw [← Category.assoc, hb', hs₀]
    exact Over.w (β (x i)))
  let u : Over.mk (Geo.Tor.spMap t) ⟶ Over.mk (Geo.Tor.spMap j) := Over.homMk (Geo.Tor.spMap io) hs₀
  let e : Fin (2 * P₀.g) → (Over.mk (Geo.Tor.spMap j) ⟶ P₀.A) := fun i => Over.homMk (b i) (hbw i)
  have he : ∀ i, u ≫ e i = β (x i) := fun i => Over.OverMorphism.ext (hb' i)
  have : IsReduced (Over.mk (Geo.Tor.spMap j)).left := inferInstanceAs (IsReduced (Sp B))
  have heM : ∀ i, e i ^ M = 1 := fun i => Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P₀.A.hom
    (by rw [Over.w, Over.w]) (Geo.Tor.spMap io) (by
      show (u ≫ e i ^ M).left = (u ≫ 1).left
      rw [comp_pow, he, comp_one, ← map_pow]
      exact congrArg (·.left) ((congrArg β (hx i)).trans (map_one β))))
  have hz : IsPrimitiveRoot z M :=
    IsPrimitiveRoot.of_map_of_injective (hzζ ▸ hζ) (Units.map_injective (f := io.toMonoidHom) hio)
  obtain ⟨κ, hκ⟩ := UnifPoint.exists_pointEquiv h.2.1
  have hg := h.1
  let c : Fin (2 * P.g) → Fin (2 * P₀.g) := Fin.cast (congrArg (2 * ·) hg)
  have hy : ∀ i, κ.symm (e i) ^ M = 1 := fun i => (map_pow κ.symm _ _).symm.trans (by rw [heM, map_one])
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ P M (unitOn z) (isPrimitiveRoot_unitOn hz)
    (fun F _ s => by
      obtain ⟨σ, rfl⟩ := Spec.map_surjective s
      have hF : (M : F) ≠ 0 := by rw [← map_natCast σ.hom]; exact (hMB.map σ.hom).ne_zero
      exact ⟨hF, (map_unitOn σ.hom z).symm ▸ isPrimitiveRoot_unitOn (isPrimitiveRoot_map σ.hom hF hz)⟩)
    (fun i => κ.symm (e (c i))) (fun i => hy _) (fun i i' => by
      obtain ⟨v, hv, -⟩ := (hL.weil _ P M _).1 _ _ (hy (c i)) (hy (c i'))
      have H := (weilIs_grpPullback_of_comm _ _ P₀.A P.A _ φ P₀.L P.L P₀.isLB P.isLB h.2.1 (LBIso.symm h.2.2) _ M _ _
        (pushPt h.2.1.1.w (κ.symm (e (c i)))) (pushPt h.2.1.1.w (κ.symm (e (c i')))) _ rfl rfl).1 hv
      have k : ∀ i, (pushPt h.2.1.1.w (κ.symm (e i))).left = (e i).left := fun i =>
        (hκ _).symm.trans (congrArg (·.left) (κ.apply_symm_apply _))
      have H₁ := CommPairing.weilIs_pull hL.globalFns P₀.isAb P₀.isLB u
        (UnifPoint.weilIs_congr (Category.id_comp _) (k _) (k _) H)
      rw [he, he] at H₁
      have e₁ := CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H₁ (hW _ _ _ _ (hw _ _))
      let v' := Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom v
      have ev : unitOn v' = v := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of B)) v.val)
      have e₂ : unitOn (Units.map io.toMonoidHom v') = unitOn ζ ^ stdSymp P₀.g (c i) (c i') := by
        rw [← map_unitOn, ev]; exact e₁
      rw [← unitOn_zpow, ← hzζ, ← map_zpow] at e₂
      have e₃ := Units.map_injective (f := io.toMonoidHom) hio (unitOn_injective e₂)
      have e₄ : stdSymp P₀.g (c i) (c i') = stdSymp P.g i i' := by simp only [stdSymp, c, Fin.val_cast, hg]
      rw [← unitOn_zpow, ← e₄, ← e₃, ev]
      exact hv)
  exact ⟨lev⟩

theorem powers_le (K : Type) [Field K] [NumberField K] : Submonoid.powers (3 : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0))

abbrev IntThird (K : Type) [Field K] [NumberField K] : Type :=
  Localization.subalgebra.ofField K (Submonoid.powers (3 : 𝓞 K)) (powers_le K)

theorem arithBase (K : Type) [Field K] [NumberField K] : ArithBase (IntThird K) K where
  ded := IsLocalization.isDedekindDomain (𝓞 K) (powers_le K) _
  ft := by
    have : Algebra.FiniteType (𝓞 K) (IntThird K) :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (3 : 𝓞 K)) _
    exact Algebra.FiniteType.trans (S := 𝓞 K) inferInstance inferInstance
  char := inferInstance
  inj := Subtype.val_injective

theorem isUnit_three (K : Type) [Field K] [NumberField K] : IsUnit ((3 : ℕ) : IntThird K) := by
  simpa only [map_ofNat, Nat.cast_ofNat] using IsLocalization.Away.algebraMap_isUnit (S := IntThird K) (3 : 𝓞 K)

theorem isUnit_three_subalgebra {K : Type} [Field K] [NumberField K] (R : Subalgebra (IntThird K) K) :
    IsUnit (3 : R) := by
  simpa only [map_ofNat, Nat.cast_ofNat] using (isUnit_three K).map (algebraMap (IntThird K) R)

theorem exists_level_hypS (hL : Laws) (m : ℕ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K)
    (R : Subalgebra (IntThird K) K) (ze : (IntThird K)ˣ) (P : PolAV (Sp R)), R.FG ∧ P.g = 1 ∧ HypS P.A P.L ∧
    Nonempty (Out.Level P (3 ^ (m + 1)) (unitOn (Units.map (algebraMap (IntThird K) R).toMonoidHom ze))) := by
  let Q := AlgebraicClosure ℚ
  let R₀ := Localization.Away (3 : ℤ)
  have h₀ : IsUnit (3 : R₀) := by
    simpa only [map_ofNat] using IsLocalization.Away.algebraMap_isUnit (S := R₀) (3 : ℤ)
  have := CMCurve.isElliptic_eisensteinCurve h₀
  have lf : ∀ (B : Type) [CommRing B], IsUnit (3 : B) → Nonempty (R₀ →+* B) := fun B _ h =>
    ⟨IsLocalization.Away.lift (3 : ℤ) (g := Int.castRingHom B) (by simpa using h)⟩
  obtain ⟨t⟩ := lf Q (Ne.isUnit three_ne_zero)
  have hM : 0 < 3 ^ (m + 1) := by positivity
  have : NeZero (3 ^ (m + 1)) := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Q (3 ^ (m + 1))
  obtain ⟨s, hs, H⟩ := exists_finite_level hL t (WeierstrassCurve.ellPolAV (CMCurve.eisensteinCurve R₀))
    (Nat.cast_ne_zero.2 hM.ne') (hζ.isUnit_unit hM.ne')
  have : Finite (insert ζ s : Set Q) := (hs.insert _).to_subtype
  have : Algebra.IsAlgebraic ℚ Q := AlgebraicClosure.isAlgebraic ℚ
  let K := IntermediateField.adjoin ℚ (insert ζ s)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have : NumberField K := {}
  let z : K := ⟨ζ, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)⟩
  have hz : IsPrimitiveRoot z (3 ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K Q) hζ (algebraMap K Q).injective
  let z' : 𝓞 K := ⟨z, hz.isIntegral hM⟩
  have hz' : IsUnit z' := IsUnit.of_pow_eq_one (Subtype.ext hz.pow_eq_one) hM.ne'
  let ze : (IntThird K)ˣ := (hz'.map (algebraMap (𝓞 K) (IntThird K))).unit
  let R : Subalgebra (IntThird K) K := Algebra.adjoin _ (Subtype.val ⁻¹' s)
  have hR : R.FG := Subalgebra.fg_def.2 ⟨_, hs.preimage Subtype.val_injective.injOn, rfl⟩
  have := (arithBase K).ded
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  have h3 : IsUnit (3 : R) := isUnit_three_subalgebra R
  have := CMCurve.isElliptic_eisensteinCurve h3
  obtain ⟨j⟩ := lf R h3
  let io : R →+* Q := (algebraMap K Q).comp R.toSubring.subtype
  have hio : Function.Injective io := Subtype.val_injective.comp Subtype.val_injective
  let zR : R := ⟨z, R.algebraMap_mem ze⟩
  have hω : IsPrimitiveRoot (zR ^ 3 ^ m) 3 :=
    (IsPrimitiveRoot.of_map_of_injective (f := io) hζ hio).pow hM (pow_succ 3 m)
  have hω' : (zR ^ 3 ^ m) ^ 2 + zR ^ 3 ^ m + 1 = 0 := by
    have := hω.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    linear_combination this
  refine ⟨K, inferInstance, inferInstance, R, ze, WeierstrassCurve.ellPolAV (CMCurve.eisensteinCurve R), hR, rfl,
    CubeRootAut.hypS_eisensteinCurve hL.cube hω', H R io j _ hio
      (IsLocalization.ringHom_ext (Submonoid.powers (3 : ℤ)) (RingHom.ext_int _ _)) (fun y hy => ?_) (Units.ext rfl)
      (by rw [Nat.cast_pow]; exact h3.pow _) _ _ (WeierstrassCurve.ellPolAV_baseChange _ j ?_)⟩
  · exact ⟨⟨⟨y, IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hy)⟩, Algebra.subset_adjoin hy⟩, rfl⟩
  · ext <;> simp [CMCurve.eisensteinCurve]

theorem exists_real_dim_one_isFractionRing : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (_ : S.Real), S.g = 1 ∧ S.Big ∧ IsFractionRing o Ω := by
  intro hL hL₂
  obtain ⟨K, _, _, R, ze, P, hR, hg, hS, ⟨lev⟩⟩ := exists_level_hypS hL 17
  have := arithBase K
  have hfr : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    exact ⟨_, R.algebraMap_mem (algebraMap (𝓞 K) _ a), _, R.algebraMap_mem (algebraMap (𝓞 K) _ b), rfl⟩
  have e : 3 ^ (17 + 1) = (3 ^ 5 * (3 ^ 2) ^ 2) ^ 2 := by norm_num
  obtain ⟨S, ρ, -, -, -, hN, hr, hSg, -⟩ := ThetaReal.exists_thetaSys_real hL hL₂ (IntThird K) K R hR hfr P 3 2 5 ze Nat.prime_three
    (by decide) le_rfl (by norm_num) (isUnit_three K) hS (e ▸ lev)
  have h1 : S.g = 1 := hSg.trans hg
  refine ⟨IntThird K, K, inferInstance, inferInstance, inferInstance, this, S, ρ, h1, ?_, inferInstance⟩
  unfold ThetaSys.Big
  rw [h1, hN, hr]
  have a : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have b : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2 - 1) ≤ 2 ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have c : (2 : ℝ) ^ (-(1 / 4) : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [Real.rpow_one] at a
  refine ⟨?_, ?_, by norm_num⟩
  · norm_num at a ⊢
    linarith
  · have d := b.trans_lt c
    generalize (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2 - 1) = u at d
    norm_num
    linarith

end GlobalTheory.RealInhabitant

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_abelian_quotient_p_divisible_smooth_group : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ p = y) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ IsAbelianScheme B ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  first | exact @GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient | exact GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient | (intros; apply GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationTest_of_geometricTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  first | exact @GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | exact GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | (intros; apply GlobalTheory.ZH.Clos.exists_core_test_of_geoTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.families_values_correspond : Laws → Laws2 → BrFamSt := by
  first | exact @GlobalTheory.Ex.brFam | exact GlobalTheory.Ex.brFam | (intros; apply GlobalTheory.Ex.brFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  first | exact @GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | exact GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | (intros; apply GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext <;> assumption)
end

