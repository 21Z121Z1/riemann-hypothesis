import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQk
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionQk

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_cubAtT {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {y : T'.left} {J} (hJ : Good D.P.L y J)
    (χ : D.X) (x w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) x w) ρ.left y J = th D y J (cP D _ χ) (ρ ≫ x) (ρ ≫ w) := by
  have := val_cub D.cub ρ hJ (cP D T χ) x w
  rwa [comp_cP] at this

theorem exists_pull (ρ : TF (R := R) F ⟶ T) (g : GtPt D T) :
    ∃ g' : GtPtF D F, g'.b = ρ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) ρ.left y J := by
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (g.s χ) ρ.left) (𝟙 _) y J = val (g.s χ) ρ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_gt (D := D) (F := F) (ρ ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) ρ.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => by
      refine Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) ?_
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
          ((MonObj.comp_mul ρ (cP D T χ) g.b).trans (congrArg (· * (ρ ≫ g.b)) (comp_cP D ρ χ)))
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ χ)
      · rfl
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') ρ.left).trans (val_mul hJ _ _ _))
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
      refine Eq.trans ?_ (val_cubAtT ρ hJ χ (cP D T χ') g.b).symm
      rw [comp_cP])
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩

theorem isIota_zero (hB : D.TauBimult) {h : GtPtF D F} (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

theorem exists_qk (hB : D.TauBimult) (ρ : TF (R := R) F ⟶ T) (k : ℕ) (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (hk : (gs k).IsZero) :
    ∃ p : QkPt D F k, p.y = 0 ∧ GtPt.IsPullF F ρ.left g p.g := by
  choose pl hb hv using fun g : GtPt D T => exists_pull ρ g
  have zero : ∀ g : GtPt D T, g.IsZero → (pl g).IsZero := fun g hg =>
    (isZero_iff _).2 ⟨by rw [hb, hg.1]; exact MonObj.comp_one (M := D.P.A) ρ, fun χ y J hJ =>
      (hv g χ y J hJ).trans ((val_corr hJ (hg.2 χ) _).trans (val_one _))⟩
  have add : ∀ g g' g'' : GtPt D T, g.IsAdd g' g'' → (pl g).IsAdd (pl g') (pl g'') := fun g g' g'' h =>
    (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, h.1]; exact MonObj.comp_mul ρ g.b g'.b, fun χ y J hJ => by
      rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) ρ.left).trans (val_mul hJ _ _ _))
      exact Eq.trans (congrArg₂ (· * ·) rfl (val_cubAtT ρ hJ χ g.b g'.b).symm) e⟩
  refine ⟨⟨0, pl g, pl (gs k), ⟨fun i => pl (gs i), zero _ h₀, fun i => add _ _ _ (hs i), rfl⟩,
    isIota_zero hB (zero _ hk)⟩, rfl, congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (hb g),
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (hv g χ y J hJ).trans ?_
  rw [val_pull hJ, Category.id_comp]

theorem base_pow (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (i : ℕ) : (gs i).b = g.b ^ i := by
  induction i with
  | zero => rw [pow_zero]; exact h₀.1
  | succ i ih => rw [pow_succ, ← ih]; exact (hs i).1

theorem torsionPoint_qk : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  intro hG R _ _ _ I hI hne D A G _ _ U k x gp hx hm
  obtain ⟨hadd, hzero⟩ := GlobalTheory.gtCoord_additive hG R I hI hne D A G U
  choose gs hgs using fun i : ℕ => (GlobalTheory.T.existsUnique_torusExtensionPoint_of_groupPoint R I hI hne D A G U (x ^ i)).exists
  have h₀ : (gs 0).IsZero := hzero _ (by simpa only [pow_zero] using hgs 0)
  have hk : (gs k).IsZero := hzero _ (by simpa only [hx] using hgs k)
  have hs : ∀ i, GtPt.IsAdd (gs i) gp (gs (i + 1)) := fun i =>
    hadd (x ^ i) x _ _ _ (hgs i) hm (by simpa only [pow_succ] using hgs (i + 1))
  exact ⟨(base_pow gp gs h₀ hs k).symm.trans hk.1,
    fun F _ _ => exists_qk D.tau_bimult (toUnit _) k gp gs h₀ hs hk⟩

end GlobalTheory.TorsionQk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory
namespace TorusGrading

theorem toSpecΓ_appLE_fromSpec {Y Z : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (g : Z ⟶ Y)
    (h : ⊤ ≤ g ⁻¹ᵁ V) : Z.toSpecΓ ≫ Spec.map (g.appLE V ⊤ h) ≫ hV.fromSpec = g := by
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  rw [← cancel_epi (⊤ : Z.Opens).ι, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem appLE_comp_top {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) (g : Z ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ V)
    {g' : W ⟶ Y} (e : s ≫ g = g') (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (g'.appLE V ⊤ h').hom u = s.appTop.hom ((g.appLE V ⊤ h).hom u) := by
  subst e
  have e : s.appTop = s.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (congrArg (fun q => q.hom u) (Scheme.Hom.appLE_comp_appLE s g V ⊤ ⊤ h le_top)).symm

theorem top_le_comp {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) {g : Z ⟶ Y} (h : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g) ⁻¹ᵁ V := fun _ _ => h trivial

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {W Z : Over S} (s : W ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (s ≫ t) χ).val = s.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_one {Z : Over S} (χ : X) : chV (1 : Z ⟶ splitTorus S X) χ = 1 := by
  rw [chV, map_one]; rfl

theorem eq_zero_of_sum_chV (Z : Over S) (s : Finset X) (h : X → Γ(Z.left, ⊤))
    (hs : ∑ χ ∈ s, (chV (fst (splitTorus S X) Z) χ).val * (snd (splitTorus S X) Z).left.appTop.hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Z s h (Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) hs)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [chV_val]
  exact congrArg (fun q => q.hom (TorusInj.chiP X Z χ))
    ((splitTorus S X ⊗ Z).left.presheaf.map_id (Opposite.op ⊤))

variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}

theorem top_le_act
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V := by
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
  refine le_trans ?_ ((lift t g).left.preimage_mono hst)
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, lift_snd]
  exact h

theorem exists_expansion (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ∃ a : X →₀ Γ(G.left, V), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ a.support, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ) := by
  let B : CommRingCat.{0} := TorusInj.GA (X := X) (V := V)
  let P : Over S := Over.mk (TorusInj.ptY (X := X) hV ≫ G.hom)
  let g₀ : P ⟶ G := Over.homMk (TorusInj.ptY (X := X) hV) rfl
  let ε : Γ(P.left, ⊤) ≅ B := Scheme.ΓSpecIso B
  let t₀ : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    (ε.inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of Γ(G.left, V) X)).toHomUnits
  have ht₀ : ∀ χ, (chV t₀ χ).val = ε.inv.hom (AddMonoidAlgebra.single χ 1) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  have hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V := (TorusInj.ptY_preimage hV).ge
  let f : AddMonoidAlgebra Γ(G.left, V) X :=
    ε.hom.hom ((((t₀ ≫ i) * g₀).left.appLE V ⊤ (top_le_act hst t₀ hg₀)).hom u)
  refine ⟨f.coeff, fun Z t g h₁ h₂ => ?_⟩
  letI : Algebra Γ(G.left, V) Γ(Z.left, ⊤) := (g.left.appLE V ⊤ h₂).hom.toAlgebra
  let φ₀ : AddMonoidAlgebra Γ(G.left, V) X →ₐ[Γ(G.left, V)] Γ(Z.left, ⊤) :=
    AddMonoidAlgebra.lift Γ(G.left, V) Γ(Z.left, ⊤) X ((Units.coeHom _).comp (splitTorusPointsEquiv S X Z t))
  let φ : B ⟶ Γ(Z.left, ⊤) := CommRingCat.ofHom φ₀.toRingHom
  have hφ : ∀ χ c, φ.hom (AddMonoidAlgebra.single χ c) = (chV t χ).val * (g.left.appLE V ⊤ h₂).hom c := fun χ c => by
    change φ₀ (AddMonoidAlgebra.single χ c) = _
    rw [AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm]; rfl
  have hσ : (Z.left.toSpecΓ ≫ Spec.map φ) ≫ TorusInj.ptY (X := X) hV = g.left := by
    rw [TorusInj.ptY, Category.assoc, ← Spec.map_comp_assoc]
    refine Eq.trans ?_ (toSpecΓ_appLE_fromSpec hV g.left h₂)
    congr 3
    exact CommRingCat.hom_ext (RingHom.ext fun c => φ₀.commutes c)
  let σ : Z ⟶ P := Over.homMk (Z.left.toSpecΓ ≫ Spec.map φ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hσ).trans (Over.w g)))
  have hσa : ∀ x : Γ(P.left, ⊤), σ.left.appTop.hom x = φ.hom (ε.hom.hom x) := fun x => by
    have : (Z.left.toSpecΓ ≫ Spec.map φ).appTop = ε.hom ≫ φ := by
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
    exact congrArg (fun q => q.hom x) this
  have hε : ∀ x : B, ε.hom.hom (ε.inv.hom x) = x := fun x => congrArg (fun q => q.hom x) ε.inv_hom_id
  have eg : σ ≫ g₀ = g := Over.OverMorphism.ext hσ
  have et : σ ≫ t₀ = t := (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => Units.ext (by
    change (chV (σ ≫ t₀) χ.toAdd).val = (chV t χ.toAdd).val
    rw [chV_comp, ht₀, hσa, hε, hφ, map_one, _root_.mul_one]))
  have ea : σ ≫ ((t₀ ≫ i) * g₀) = (t ≫ i) * g := by
    rw [MonObj.comp_mul, ← Category.assoc, et, eg]
  rw [appLE_comp_top σ.left _ (top_le_act hst t₀ hg₀) (congrArg (fun q => q.left) ea) h₁ u, hσa]
  change φ.hom f = _
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => hφ χ _

theorem exists_point (hV : IsAffineOpen V) : ∃ (Z : Over S) (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ V),
    Function.Injective (g.left.appLE V ⊤ h).hom := by
  refine ⟨Over.mk (hV.fromSpec ≫ G.hom), Over.homMk hV.fromSpec rfl, hV.fromSpec_preimage_self.ge, ?_⟩
  have h1 : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  change Function.Injective (hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge).hom
  rw [h1]
  exact (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective

omit [GrpObj G] in
theorem val_comp {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ((s ≫ g).left.appLE V ⊤ h').hom u = s.left.appTop.hom ((g.left.appLE V ⊤ h).hom u) :=
  appLE_comp_top s.left g.left h (Over.comp_left _ _ _ s g).symm h' u

omit [GrpObj G] in
theorem val_congr {Z : Over S} {g g' : Z ⟶ G} (e : g = g') (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ g'.left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : (g.left.appLE V ⊤ h).hom u = (g'.left.appLE V ⊤ h').hom u := by
  subst e; rfl

omit [GrpObj G] in
theorem top_le_comp_left {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V := by
  rw [Over.comp_left]; exact top_le_comp s.left h

theorem isWt_of_expansion [IsMonHom i]
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) {χ : X} (hχ : χ ∈ s) : IsWt i V (a χ) χ := by
  intro Z t g h₁ h₂
  rw [← chV_val, ← sub_eq_zero]
  refine eq_zero_of_sum_chV Z s (fun χ => (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (a χ) -
    (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z = p
  generalize snd (splitTorus S X) Z = q
  have k₁ := top_le_comp_left q h₁
  have k₂ := top_le_comp_left q h₂
  have e : (p ≫ i) * (q ≫ ((t ≫ i) * g)) = ((p * (q ≫ t)) ≫ i) * (q ≫ g) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  have a₁ := ha _ p _ (top_le_act hst p k₁) k₁
  have a₂ := ha _ (p * (q ≫ t)) _ (top_le_act hst _ k₂) k₂
  have a₃ := (a₁.symm.trans (val_congr e _ _ u)).trans a₂
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at a₃
  refine Eq.trans (Finset.sum_congr rfl fun ψ _ => ?_) a₃
  rw [val_comp q h₁ k₁, val_comp q h₂ k₂, chV_mul, Units.val_mul, chV_comp, map_sub, map_mul, mul_sub,
    _root_.mul_assoc]

theorem eq_zero_of_sum_isWt (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {s : Finset X} {a : X → Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) (hs : ∑ χ ∈ s, a χ = 0) {χ : X}
    (hχ : χ ∈ s) : a χ = 0 := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj (Eq.trans ?_ (map_zero _).symm)
  refine eq_zero_of_sum_chV Z₀ s (fun χ => (g₀.left.appLE V ⊤ h₀).hom (a χ)) ?_ χ hχ
  generalize fst (splitTorus S X) Z₀ = p
  generalize snd (splitTorus S X) Z₀ = q
  have k := top_le_comp_left q h₀
  have := congrArg (((p ≫ i) * (q ≫ g₀)).left.appLE V ⊤ (top_le_act hst p k)).hom hs
  rw [map_sum, map_zero] at this
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) this
  rw [ha χ _ p (q ≫ g₀) _ k, ← chV_val, val_comp q h₀ k]

theorem eq_sum_of_expansion [IsMonHom i] (hV : IsAffineOpen V)
    {u : Γ(G.left, V)} {s : Finset X} {a : X → Γ(G.left, V)}
    (ha : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ s, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ)) : u = ∑ χ ∈ s, a χ := by
  obtain ⟨Z₀, g₀, h₀, inj⟩ := exists_point hV
  refine inj ?_
  have e : ((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀ = g₀ := by rw [MonObj.one_comp, _root_.one_mul]
  have h₁ : ⊤ ≤ (((1 : Z₀ ⟶ splitTorus S X) ≫ i) * g₀).left ⁻¹ᵁ V := by rw [e]; exact h₀
  rw [map_sum, ← val_congr e h₁ h₀ u, ha Z₀ 1 g₀ h₁ h₀]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [chV_one, Units.val_one, _root_.one_mul]

end TorusGrading

open TorusGrading in

theorem functions_graded_by_weights :
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by
  intro S G _ X _ i hi V hV hst
  refine ⟨fun u => ?_, fun a ha hs => ?_⟩
  · obtain ⟨a, ha⟩ := exists_expansion hV hst u
    refine ⟨a, fun χ => ?_, eq_sum_of_expansion hV ha⟩
    by_cases hχ : χ ∈ a.support
    · exact isWt_of_expansion hst ha hχ
    · rw [Finsupp.notMem_support_iff.1 hχ]
      exact isWt_zero χ
  · refine Finsupp.ext fun χ => ?_
    by_contra h
    exact h (eq_zero_of_sum_isWt hV hst ha hs (Finsupp.mem_support_iff.2 h))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharAgree

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem comp_q_eq_one_iff (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a : Z ⟶ thickObj R I e G) :
    a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] ↔
      a.left ≫ g.pG.left = a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
  have h1 : (a ≫ g.q).left ≫ pullback.fst D.P.A.hom (thick R I e) = a.left ≫ g.pG.left :=
    Category.assoc _ _ _
  have h2 : (toUnit Z ≫ η[thickObj R I e D.P.A]).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
    have k1 := UnitValue.eSec_pullback_fst (thick R I e) D.P.A
    have k2 : (toUnit Z).left = a.left ≫ pullback.snd G.hom (thick R I e) :=
      ((Category.comp_id _).symm.trans (Over.w (toUnit Z))).trans (Over.w a).symm
    have k3 : pullback.fst G.hom (thick R I e) ≫ G.hom =
        pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg ((toUnit Z).left ≫ ·) k1).trans ?_)
    refine (congrArg (· ≫ thick R I e ≫ eSec D.P.A) k2).trans ((Category.assoc _ _ _).trans ?_)
    refine congrArg (a.left ≫ ·) ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ eSec D.P.A) k3.symm).trans (Category.assoc _ _ _)
  refine ⟨fun h => h1.symm.trans ((congrArg (fun φ => φ.left ≫ _) h).trans h2), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext (h1.trans (h.trans h2.symm)) ?_)
  exact (Over.w _).trans (Over.w _).symm

def Match (g : GtCoord I D e G) (g' : GtCoord I D' e G) (xe : D'.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
    r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
    ∀ x, val (g.t (xe x)) r z J = val (g'.t x) r z J'

omit [IsDomain R] in
theorem connected_thick [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) :
    ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint _) fun y _ => ?_⟩
    exact ⟨closure {y}, Set.subset_univ _,
      (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
      isPreconnected_singleton.closure⟩
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

variable [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
include hI

theorem exists_torus_iso (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ θ : splitTorus _ D'.X ≅ splitTorus _ D.X, IsMonHom θ.hom ∧ θ.hom ≫ g.i = g'.i := by
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have m' : Mono g'.i := ⟨fun a b h => g'.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have := g.i_hom
  have := g'.i_hom
  let u := g.isKernel.lift g'.i (toUnit _) (gtCoord_i_comp_q hI g g')
  let v := g'.isKernel.lift g.i (toUnit _) (gtCoord_i_comp_q hI g' g)
  have hu : u ≫ g.i = g'.i := g.isKernel.lift_fst _ _ _
  have hv : v ≫ g'.i = g.i := g'.isKernel.lift_fst _ _ _
  refine ⟨⟨u, v, ?_, ?_⟩, ⟨?_, ?_⟩, hu⟩
  · rw [← cancel_mono g'.i, Category.assoc, hv, hu, Category.id_comp]
  · rw [← cancel_mono g.i, Category.assoc, hu, hv, Category.id_comp]
  · change η ≫ u = η
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.one_hom, IsMonHom.one_hom]
  · change μ ≫ u = (u ⊗ₘ u) ≫ μ
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, hu]

theorem exists_match (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ xe : D'.X ≃+ D.X, Match g g' xe := by
  obtain ⟨θ, hθ, hi⟩ := exists_torus_iso hI g g'
  have := connected_thick hI e
  obtain ⟨xe, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.X D'.X θ hθ
  refine ⟨xe, fun Z r z J J' hJ hJ' _ h' x => ?_⟩
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let a : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g'.isKernel.lift a (toUnit _) ((comp_q_eq_one_iff g' a).2 h')
  have hτ : τ ≫ g'.i = a := g'.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ θ.hom) ≫ g.i = a := by rw [Category.assoc, hi, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ θ.hom) 1 z J hJ (xe x)).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D' e G g' FinalForm τ 1 z J' hJ' x).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))

theorem match_unique (g : GtCoord I D e G) (g' : GtCoord I D' e G) {f f' : D'.X → D.X}
    (h : Match g g' f) (h' : Match g g' f') : f = f' := by
  funext x
  have := connected_thick hI e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J' hJ' using fun ψ : (splitTorus _ D.X).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have c := (comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have c' := (comp_q_eq_one_iff g' g.i).1 (gtCoord_i_comp_q hI g' g)
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J J' hJ hJ' c c' x).trans
    (h' _ _ z J J' hJ hJ' c c' x).symm).trans (k _))

omit hI [IsLocalRing R] [IsNoetherianRing R] in

theorem match_down {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G) {f : D'.toPre.X → D.toPre.X}
    (h : Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))

end CharAgree

open CharAgree in

theorem unifPre_characterGroup_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G), ∃ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U'
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.toPre.X → D.toPre.X), Match (U.gt e) (U'.gt e) f →
      Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

end GlobalTheory
end

