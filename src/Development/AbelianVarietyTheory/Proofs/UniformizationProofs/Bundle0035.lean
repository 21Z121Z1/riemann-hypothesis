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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RangeSubsetOfForallField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem corr_of_thick {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := by
    refine Units.ext (AbelianPartIso.fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, map_one, mul_eq_right.1 this.symm]
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable (I) in

abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (𝟙 _)

variable (I) in

abbrev levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I e) ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

omit [IsDomain R] in
theorem levι_left (e : ℕ) : (levι I e).left = thick R I e :=
  (Category.comp_id _).symm.trans ((Over.w (levι I e)).trans (Category.id_comp _))

omit [IsDomain R] in
theorem toUnit_left (e : ℕ) : (toUnit (Over.mk (thick R I e))).left = thick R I e :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (thick R I e))))

def Lifts {e : ℕ} (g : GtCoord I D e G) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (a : lev I e ⟶ thickObj R I e G) : Prop :=
  pushHom (isGrpPullback_pullback G (thick R I e)) (lev I e) a = levι I e ≫ x ∧ im g a = levι I e ≫ gp.b ∧
    ∀ χ z J, Good D.P.L z J → val (g.t χ) a.left z J = val (gp.s χ) (levι I e).left z J

theorem exists_lifts {e : ℕ} (g : GtCoord I D e G) {x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G}
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G),
      xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ g.pG = toUnit _ ≫ gp.b ∧
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) xe.left)
        (LB.pullGen D.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) :
    ∃ a, Lifts g x gp a := by
  obtain ⟨xe, h₁, h₂, h₃⟩ := h
  have hw : xe.left ≫ (thickObj R I e G).hom = 𝟙 _ := by
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact (Over.w xe).trans (Category.id_comp _).symm
  have hu : (toUnit (Over.mk (thick R I e))).left = (levι I e).left := (toUnit_left e).trans (levι_left e).symm
  refine ⟨Over.homMk xe.left hw, Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_, fun χ z J hJ => ?_⟩
  · exact (congrArg (·.left) h₁).trans (congrArg (· ≫ x.left) hu)
  · exact (congrArg (·.left) h₂).trans (congrArg (· ≫ gp.b.left) hu)
  · have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp, hu] at this
    exact this

omit [IsDomain R] [IsCommMonObj G] in
theorem push_injective {e : ℕ} {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    Function.Injective (pushHom (isGrpPullback_pullback G (thick R I e)) T) := fun a b h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (·.left) h) ((Over.w a).trans (Over.w b).symm))

omit [IsDomain R] in

theorem pt_ext [IsLocalRing R] [IsHausdorff I R] {B : Over (Spec (CommRingCat.of R))}
    {b b' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B} (h : ∀ e, levι I e ≫ b = levι I e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e =>
    (congrArg (· ≫ b.left) (levι_left e)).symm.trans
      ((congrArg (·.left) (h e)).trans (congrArg (· ≫ b'.left) (levι_left e))))

theorem prod_gtφT {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (DegPre.cT D T χ * b).left)⁻¹ * h (DegPre.cT D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) = _
  rw [zpow_neg_one, zpow_neg_one, zpow_one, zpow_one]
  rfl

variable [IsLocalRing R] [IsNoetherianRing R] [IsHausdorff I R]

theorem isAdd_of_lifts (hGF : GlobalFnsSt) (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} {gp gp' gp'' : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) x gp a) (h' : ∀ e, ∃ a, Lifts (g e) x' gp' a)
    (h'' : ∀ e, ∃ a, Lifts (g e) (x * x') gp'' a) : GtPt.IsAdd gp gp' gp'' := by
  choose a ha using h
  choose a' ha' using h'
  choose a'' ha'' using h''
  have hm : ∀ e, a'' e = a e * a' e := fun e => push_injective (by
    rw [map_mul, (ha e).1, (ha' e).1, (ha'' e).1]
    exact MonObj.comp_mul _ _ _)
  have hb : gp''.b = gp.b * gp'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (ha e).2.1, ← (ha' e).2.1, ← (ha'' e).2.1, hm, im_mul]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen χ) (gp'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (prod_gtφT gp''.b χ h) (prod_cub (DegPre.cT D _ χ) gp.b gp'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (prod_gtφT gp.b χ h) (prod_gtφT gp'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have k := val_t_mul_points (g e) hGF χ (a e) (a' e) z J hJ
    have c : cubeVal (g e) χ z J (a e) (a' e) =
        cubV D.cub z J (levι I e ≫ DegPre.cT D _ χ) (levι I e ≫ gp.b) (levι I e ≫ gp'.b) := by
      unfold cubeVal
      rw [(ha e).2.1, (ha' e).2.1, comp_toUnit_assoc]
    rw [← hm, (ha e).2.2 χ z J hJ, (ha' e).2.2 χ z J hJ, (ha'' e).2.2 χ z J hJ, c] at k
    have := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I e) hJ _ _ _))).trans
      (k.trans (val_mul hJ _ _ _).symm)
    rw [levι_left] at this
    exact this

theorem isZero_of_lifts (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) 1 gp a) : gp.IsZero := by
  choose a ha using h
  have hm : ∀ e, a e = 1 := fun e => push_injective (by
    rw [map_one, (ha e).1]
    exact MonObj.comp_one _)
  have hb : gp.b = 1 := pt_ext (I := I) fun e => by
    rw [MonObj.comp_one, ← (ha e).2.1, hm, im_one]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_) (gp.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (prod_gtφT gp.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · have k := (ha e).2.2 χ z J hJ
    rw [hm, val_unit (g e) χ hJ, levι_left] at k
    exact k.symm.trans (val_one _).symm

end GlobalTheory.CoordAdd

namespace GlobalTheory

open CoordAdd in

theorem gtCoord_additive : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), (∀ (x x' : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' gp'' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x' ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x * x') ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp''.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp''.s χ) (toUnit (Over.mk (thick R I e))).left)) → GtPt.IsAdd gp gp' gp'') ∧ ∀ gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (1 : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.IsZero := by
  intro hGF R _ _ _ I hR hI D A G _ _ U
  obtain ⟨_, -, -, _⟩ := hR
  exact ⟨fun x x' gp gp' gp'' h h' h'' => isAdd_of_lifts hGF hI U.gt (fun e => exists_lifts _ (h e))
    (fun e => exists_lifts _ (h' e)) (fun e => exists_lifts _ (h'' e)),
    fun gp h => isZero_of_lifts hI U.gt fun e => exists_lifts _ (h e)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDimension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem nonempty_linearEquiv_of_rel {F M N : Type*} [Semiring F] [AddCommMonoid M] [AddCommMonoid N] [Module F M]
    [Module F N] (P : M → N → Prop) (h₁ : ∀ m, ∃! n, P m n) (h₂ : ∀ n, ∃! m, P m n)
    (ha : ∀ m n m' n', P m n → P m' n' → P (m + m') (n + n')) (hs : ∀ (c : F) m n, P m n → P (c • m) (c • n)) :
    Nonempty (M ≃ₗ[F] N) := by
  choose f hf hf' using h₁
  let g : M →ₗ[F] N :=
    { toFun := f
      map_add' := fun m m' => (hf' _ _ (ha _ _ _ _ (hf m) (hf m'))).symm
      map_smul' := fun c m => (hf' _ _ (hs c _ _ (hf m))).symm }
  refine ⟨LinearEquiv.ofBijective g ⟨fun m m' e => ?_, fun n => ?_⟩⟩
  · have e' : f m = f m' := e
    exact (h₂ (f m')).unique (e' ▸ hf m) (hf m')
  · obtain ⟨m, hm, -⟩ := h₂ n
    exact ⟨m, (hf' _ _ hm).symm⟩

section Comb

variable {X Y : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j

theorem exists_isComb {M : LB Y} (b : Fin n → LB.Sec M) (a : Fin n → Γ(Y, ⊤)) : ∃ s, IsComb b a s :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isComb_iff_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (a : Fin n → Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) :
    IsComb b a s ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (a i) * sval (b i) (𝟙 Y) y J := by
  refine ⟨fun h y J hJ => SectionScalarValuation.sval_lin a b h _ y hJ, fun h j => ?_⟩
  obtain ⟨t, ht⟩ := exists_isComb b a
  rw [← ht j]
  exact sec_ext_val hL (fun y J hJ => (h y J hJ).trans (SectionScalarValuation.sval_lin a b ht _ y hJ).symm) j

theorem exists_basis_of_gen (hL : L.IsLB) {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => g (c i)) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => 𝟙 Y ≫ φ' k) φ₃) (Sum.elim ε' fun k => -ε₃ k) φ ε := fun U _ w => by
    have := h U w
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
    rw [← this]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL h (pullMulSec (b i) (𝟙 Y) u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := invGen_isGen L _ _ u hu
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
  refine (existsUnique_congr fun c => ?_).1 (hb t)
  rw [isComb_iff_sval hL, isComb_iff_sval hL]
  refine forall₃_congr fun y J hJ => ?_
  rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_inv, Category.id_comp, Units.mul_inv_eq_iff_eq_mul,
    Finset.sum_mul]
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]

end Comb

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_basis_famSec (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → FamFree.FamSec D F k α,
      ∀ s, ∃! c : Fin (k ^ D.P.g) → F, IsComb b (fun i => gF D F (c i)) s := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  refine exists_basis_of_gen D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) u hu (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc]) (gF D F) b (fun s => ?_)
  exact (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toEquiv) fun _ => Iff.rfl).2 (hb s)

theorem nonempty_fam_equiv (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Nonempty (Fam D F k ≃ₗ[F] (D.X ⧸ FamFree.multiples D k → Fin (k ^ D.P.g) → F)) := by
  let rep : D.X ⧸ FamFree.multiples D k → D.X := Quotient.out
  have hrep : ∀ c, QuotientAddGroup.mk (rep c) = c := fun c => Quotient.out_eq c
  choose b hb using fun c => exists_basis_famSec (D := D) (F := F) hT hk (rep c)
  refine nonempty_linearEquiv_of_rel
    (fun s z => ∀ c, IsComb (b c) (fun i => gF D F (z c i)) (s.s (rep c))) (fun s => ?_) (fun z => ?_) ?_ ?_
  · choose z hz hz' using fun c => hb c (s.s (rep c))
    exact ⟨z, hz, fun z' h => funext fun c => hz' c _ (h c)⟩
  · choose σ hσ using fun c => exists_isComb (b c) (fun i => gF D F (z c i))
    refine (existsUnique_congr fun s => forall_congr' fun c => ?_).1
      (FamFree.existsUnique_fam hG hB hk rep hrep σ)
    exact ⟨fun h => h ▸ hσ c, fun h => SecOps.sec_ext fun j => (h j).trans (hσ c j).symm⟩
  · intro s z s' z' h h' c j
    rw [add_f, h c j, h' c j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, map_add, resTop, add_mul]
  · intro a s z h c j
    rw [smul_f, h c j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, resTop, _root_.mul_assoc]

theorem finrank_fam (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) :
    Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  obtain ⟨e⟩ := nonempty_fam_equiv (D := D) (F := F) hG hT hB hk
  have hc : Nat.card (D.X ⧸ FamFree.multiples D k) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  have : Finite (D.X ⧸ FamFree.multiples D k) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite (D.X ⧸ FamFree.multiples D k)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_fin_fun, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hc, smul_eq_mul, pow_add]

theorem main : GlobalFnsSt → CubeSt → SquareSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D.toPre F k) ∧ Module.finrank F (Fam D.toPre F k) = k ^ (D.toPre.rank + D.toPre.P.g) :=
  fun hG _ _ hT _ _ _ _ D _ _ _ _ hk => finrank_fam hG hT D.tau_bimult hk

end GlobalTheory.FamDimension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyTorusExtensionSplitTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MultiplicativeReduction

open GlobalTheory.WeierstrassCurve

theorem isProper_pullback_snd {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    {K : Type} [Field K] (f : R →+* K) (hΔ : f W.Δ ≠ 0) :
    IsProper (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f))) := by
  have hpb : IsPullback (mapHom W f rfl ∣_ U) ((mapHom W f rfl ⁻¹ᵁ U).ι ≫ toSpec (W.map f))
      (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  have htop : mapHom W f rfl ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    let k := (scheme (W.map f)).residueField x
    obtain ⟨ρ, P, h, hx⟩ : ∃ (ρ : K →+* k) (P : Fin 3 → k)
        (h : IsUnimodularSol ((W.map f).map ρ) P),
        (scheme (W.map f)).fromSpecResidueField x = ptHom (W.map f) ρ P h := by
      obtain ⟨g, hg⟩ := Spec.map_surjective
        ((scheme (W.map f)).fromSpecResidueField x ≫ toSpec (W.map f))
      exact ⟨g.hom, exists_eq_ptHom (W.map f) (A := k) g.hom _ hg.symm⟩
    have hE : ((W.map f).map ρ).IsElliptic := ⟨by
      rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
      exact (IsUnit.mk0 _ hΔ).map ρ⟩
    have h1 := (hU k (ρ.comp f) P (h.comp_of_map_eq rfl)).mpr h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage, ← hx] at h1
    have h2 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) ∈
        mapHom W f rfl ⁻¹ᵁ U := h1 (Set.mem_univ (IsLocalRing.closedPoint k))
    have h3 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) = x :=
      Scheme.fromSpecResidueField_apply x _
    exact h3 ▸ h2
  have : IsIso (mapHom W f rfl ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Scheme.topIso _).hom)
  rw [← hpb.isoPullback_inv_snd]
  infer_instance

theorem nonempty_torusExtension_splitTorus (K : Type) [Field K] :
    Nonempty (TorusExtension (splitTorus (Spec (CommRingCat.of K)) ℤ)) :=
  ⟨Geo.Tor.torusExtOfIso (GlobalTheory.Diag.baseChangeIso (𝟙 (Spec (CommRingCat.of K))) ℤ)
    (GlobalTheory.Diag.torusExtension _ ℤ (𝟙 _))⟩

theorem isSemiAbelian_and_specialFibre : ∀ (W : WeierstrassCurve (PowerSeries ℚ)), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : PowerSeries ℚ →+* K), f PowerSeries.X = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : PowerSeries ℚ →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f PowerSeries.X = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * PowerSeries.X : PowerSeries ℚ) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp

end GlobalTheory.MultiplicativeReduction
end

