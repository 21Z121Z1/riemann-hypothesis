import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabTrans

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

section Ext

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] {k : ℕ}

theorem qkExt_trans {f : F →+* F'} {g : F' →+* F''} {p : QkPt D F k} {q : QkPt D F' k} {r : QkPt D F'' k}
    (h₁ : QkExt f p q) (h₂ : QkExt g q r) : QkExt (g.comp f) p r := by
  have hs : spMap (g.comp f) = spMap g ≫ spMap f := Geo.Tor.spMap_comp _ _
  refine ⟨h₂.1.trans h₁.1, by rw [h₂.2.1, h₁.2.1, hs, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine ((val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    (val_pull hJ _ _ _)))).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact congrArg (fun s => val (p.g.s χ) s y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hs.symm))

theorem qkExt_inj (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p q : QkPt D F k} {r : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom q r) : p = q := by
  have e := ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).symm.trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂)
  exact qk_ext (congrArg QkPt.y e :) (gtExt_injective _ f.comp_algebraMap (congrArg QkPt.g e))

theorem exists_ext (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') (p : QkPt D F k) : ∃ r, QkExt f.toRingHom p r :=
  ⟨_, (qkExt_iff hB _ f.comp_algebraMap _ _).2 rfl⟩

theorem ext_unique (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p : QkPt D F k} {r r' : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom p r') : r = r' :=
  ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂).symm

theorem exists_of_ext [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F')
    (hk : 1 ≤ k) (r : QkPt D F' k) : ∃ p : QkPt D F k, QkExt f.toRingHom p r := by
  have : CharZero F := (RingHom.charZero_iff (algebraMap (FractionRing R) F).injective).1 inferInstance
  obtain ⟨p, hp⟩ := exists_qkExt f.toRingHom f.comp_algebraMap hB GlobalTheory.firstFiveLaws.1 (Nat.cast_ne_zero.2 (by omega)) r
  exact ⟨p, (qkExt_iff hB _ f.comp_algebraMap _ _).2 hp.symm⟩

end Ext

theorem exists_lift_pt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ga : FractionRing R →+* FractionRing R'}
    {A : Over (Sp (FractionRing R))} {A' : Over (Sp (FractionRing R'))} {a : A'.left ⟶ A.left}
    (h : IsPullback a A'.hom A.hom (spMap ga)) {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F'] (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = (algebraMap _ F').comp ga)
    (x : TFK (R := R) F ⟶ A) : ∃ x' : TFK (R := R') F' ⟶ A', x'.left ≫ a = spMap f ≫ x.left := by
  have w : (spMap f ≫ x.left) ≫ A.hom = jFK (R := R') F' ≫ spMap ga := by
    rw [Category.assoc, Over.w x]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap hf).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

theorem eq_fracMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {ga : FractionRing R →+* FractionRing R'}
    (h : ∀ r, ga (algebraMap R _ r) = algebraMap R' _ (φ r)) : ga = fracMap hφ :=
  IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (h r).trans (fracMap_algebraMap hφ r).symm)

theorem exists_fib_cancel {S S' S₀ S₁ : Scheme.{0}} {A : PolAV S} {A' : PolAV S'} {A₀ : PolAV S₀} {A₁ : PolAV S₁}
    {f : S' ⟶ S} {f₀ : S₀ ⟶ S} {g : S₁ ⟶ S₀} {g' : S₁ ⟶ S'} (sq : g' ≫ f = g ≫ f₀)
    {a : A'.A.left ⟶ A.A.left} {a₀ : A₀.A.left ⟶ A.A.left} {b : A₁.A.left ⟶ A₀.A.left}
    (ha : IsGrpPullback A'.A A.A f a) (la : LBIso A'.L (A.L.pull a))
    (ha₀ : IsGrpPullback A₀.A A.A f₀ a₀) (la₀ : LBIso A₀.L (A.L.pull a₀))
    (hb : IsGrpPullback A₁.A A₀.A g b) (lb : LBIso A₁.L (A₀.L.pull b)) :
    ∃ a₁ : A₁.A.left ⟶ A'.A.left, a₁ ≫ a = b ≫ a₀ ∧ IsGrpPullback A₁.A A'.A g' a₁ ∧ LBIso A₁.L (A'.L.pull a₁) := by
  have n := (hb.comp ha₀).congr sq.symm rfl
  have w : (b ≫ a₀) ≫ A.A.hom = (A₁.A.hom ≫ g') ≫ f := n.1.w.trans (Category.assoc _ _ _).symm
  have e := ha.1.lift_fst _ _ w
  refine ⟨ha.1.lift _ _ w, e, IsGrpPullback.cancel ha (n.congr rfl e.symm) (ha.1.lift_snd _ _ w), ?_⟩
  have l₁ : LBIso (A₀.L.pull b) (A.L.pull (b ≫ a₀)) :=
    la₀.chartPull (Geo.Tor.chartPullPull A₀.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a₀) _ b fun _ => rfl)
  have l₂ : LBIso (A'.L.pull (ha.1.lift _ _ w)) (A.L.pull (b ≫ a₀)) :=
    la.chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a) _ _ fun _ => e.symm)
  exact LBIso.trans A₁.isLB (pull_isLB A.isLB _) (pull_isLB A'.isLB _)
    (LBIso.trans A₁.isLB (pull_isLB A₀.isLB _) (pull_isLB A.isLB _) lb l₁) l₂.symm

theorem nonempty_lift (K F : Type) [Field K] [Field F] [IsAlgClosed F] [Algebra K F] :
    Nonempty (AlgebraicClosure K →ₐ[K] F) := ⟨IsAlgClosed.lift⟩

end GlobalTheory.LabTrans

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelAfterExt

theorem weilIs_of_ext {O C : Type} [Field O] [Field C] (β : O →+* C) {Q : PolAV (Sp O)}
    {Q' : PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left} (hQ : IsPolFibre β Q Q' ψ)
    (n : ℕ) (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (u : Oˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hw : WeilIs Q'.A Q'.L n (ObjPull.secPull hQ.2.1 x) (ObjPull.secPull hQ.2.1 y)
      (unitOn (Units.map β.toMonoidHom u))) : WeilIs Q.A Q.L n x y (unitOn u) := by
  have H := hQ.2.1
  have := Q.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (spMap β) (Category.comp_id _)
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hQ.2.2.symm _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (ObjPull.secPull_left H x) (ObjPull.secPull_left H y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (β.injective h₅)
  exact hc

theorem exists_ext_torsion (K : Type) [Field K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (σ : K'' →+* Ω) (Q : PolAV (Sp Ω)) (ψσ : Q.A.left ⟶ P.A.left) (hQ : IsPolFibre σ P Q ψσ),
        ∀ y, y ^ N = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y := by
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points K (torsion P₀.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp K) P₀.A P₀.isAb N hN).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro K'' Ω _ _ i f hf P ψ hP σ Q ψσ hQ y hy
  letI : Algebra K' K'' := i.toAlgebra
  letI : Algebra K K'' := f.toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq' hf.symm
  have hPg : IsGrpPullback P.A P₀.A (spMap f) ψ := hP.2.1
  have hQg : IsGrpPullback Q.A P.A (spMap σ) ψσ := hQ.2.1
  let x0 := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hx0 : x0 ^ N = 1 := by simp only [x0, ← map_pow, hy, map_one]
  have hx0l : x0.left = (y.left ≫ ψσ) ≫ ψ := rfl
  have hmul : x0 ≫ mulN P₀.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx0, Hom.one_def]
  let t0 : _ ⟶ torsion P₀.A N := pullback.lift x0 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι P₀.A N = x0 := pullback.lift_fst _ _ _
  have hs : ((𝟙_ (Over (Sp Ω))).hom ≫ spMap σ) ≫ spMap f = spMap (σ.comp f) := by
    rw [Category.assoc, spMap_comp_spMap]
    exact Category.id_comp _
  obtain ⟨w, hw⟩ := H K'' Ω σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion P₀.A N).hom = (𝟙_ (Over (Sp K''))).hom ≫ spMap f := by
    refine spec_map_field_cancel σ _ _ ?_
    rw [← Category.assoc, hw, Over.w t0]
    refine hs.trans ?_
    rw [← spMap_comp_spMap]
    exact congrArg (spMap σ ≫ ·) (Category.id_comp _).symm
  let w1 : Over.mk ((𝟙_ (Over (Sp K''))).hom ≫ spMap f) ⟶ P₀.A :=
    Over.homMk (w ≫ (torsion.ι P₀.A N).left) (by rw [Category.assoc, Over.w, hw2]; rfl)
  let x := (ObjPull.pushEquiv hPg (𝟙_ _)).symm w1
  have hxl : x.left ≫ ψ = w ≫ (torsion.ι P₀.A N).left := ObjPull.pushEquiv_symm_left hPg _ w1
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← Category.assoc, hw, ← Over.comp_left, ht0, hx0l]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem exists_ext_level (K : Type) [Field K] [CharZero K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' : Type) [Field K''] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (g : ℕ), P.g = g → ∀ ze : K''ˣ, IsPrimitiveRoot (ze : K'') N →
      ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K'')) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
        (∀ x, lev x ^ N = 1) ∧ ∀ x y, WeilIs P.A P.L N (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_torsion K P₀ N hN
  refine ⟨K', inferInstance, inferInstance, hfin, fun K'' _ i f hf P ψ hP g hg ze hze => ?_⟩
  let Ω := AlgebraicClosure K''
  let σ : K'' →+* Ω := algebraMap K'' Ω
  haveI : CharZero Ω := (σ.comp f).charZero_iff (σ.comp f).injective |>.1 inferInstance
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 σ P
  obtain ⟨l, h₁, h₂, h₃⟩ := SiegPt.exists_level (O := Ω) (C := Ω) Q g N (Units.map σ.toMonoidHom ze) (hQ.1.trans hg)
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))) (hze.map_of_injective σ.injective)
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H K'' Ω i f hf P ψ hP σ Q φ hQ (l a) (h₂ a)
  have tors : ∀ a, t a ^ N = 1 := fun a => hinj (by rw [map_pow, ht, map_one, h₂])
  refine ⟨t, fun a b => hinj ?_, tors, fun a b => weilIs_of_ext σ hQ N _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, h₁]
  · rw [ht, ht, map_zpow]
    exact h₃ a b

open GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (A' : PolAV (Sp (FractionRing R')))
    (gA : A'.A.left ⟶ A.A.left) (hA : IsPolFibre (fracMap hg) A A' gA) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre),
      Nonempty (Unif I' D' A' ((Over.pullback (specOf g)).obj G)) := by
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨dA, gpA, tA⟩ := hA
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, -, -⟩ := h4.unifBaseChange R R' I I' hR hR' g hI D A G hG U Wo hψ hgen
    ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, ⟨U'⟩⟩

end GlobalTheory.LevelAfterExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QLevelRescale
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qkPt_rescale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  intro o Ω _ _ _ S ρ p _ y₀ u k k' d pk x hk hd hk' hx
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  have e : k' • pk.g = iota hB (PadicAlgCl p) (d • pk.y) := by
    rw [hk', ← smul_smul, qk_nsmul hB, map_nsmul]
  refine ⟨qkMk hB (d • pk.y) pk.g e, rfl, ?_⟩
  have L := GlobalTheory.PeriodsAnyChar.qkToAkU_level GlobalTheory.firstFiveLaws u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p)
    k d k' hk hd (by rw [hk', Nat.mul_comm]) pk (qkMk hB (d • pk.y) pk.g e) x
  exact (L.1 rfl rfl).1 hx

end GlobalTheory.QLevelRescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquare
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem nonempty_level_algClosed (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (M : ℕ)
    (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) : Nonempty (Level P M ze) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let z' : Kˣ := Units.map e.hom.hom.toMonoidHom ze
  have hz' : IsPrimitiveRoot z' M := hz.map_of_injective (f := Units.map e.hom.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso e.hom).1)
  have hze : unitOn z' = ze := Units.ext (e.hom_inv_id_apply (ze : Γ(Sp K, ⊤)))
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P M hM z' hz'
  rw [hze] at hw
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P M ze hz
    (fun F _ s => by
      have := nt F
      refine ⟨?_, ?_⟩
      · rw [← map_natCast (Spec.preimage s).hom]; exact (map_ne_zero _).2 hM
      · rw [← hze]
        exact hz'.map_of_injective (f := Units.map (s.appTop.hom.comp e.inv.hom).toMonoidHom)
          (Units.map_injective (RingHom.injective _)))
    pt hpt hw
  exact ⟨lev⟩

theorem exists_level_isThetaPt_of_hasTh : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (rig : LB.Gen (P.L.pull (eSec P.A))) (g m N : ℕ) (hg : P.g = g) (c : Fin N → K) (ze : Γ(Sp K, ⊤)ˣ), rig.IsGen → Odd m → (m : K) ≠ 0 → IsPrimitiveRoot ze (m ^ 2) → HasTh P.A P.L rig m (𝟙 (Sp K)) c → ∃ (lev : Out.Level P (m ^ 2) ze) (β : (Fin (2 * g) → ZMod (m ^ 2)) → Fin N), ∀ mu : K, mu ≠ 0 → IsThetaPt P m (levelPoint lev hg) (fun a => GlobalTheory.ZH.fn (mu * c (β a))) := by
  intro K _ _ P rig g m N hg c ze hrig hm hK hze hc
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hK2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hK
  obtain ⟨lev⟩ := nonempty_level_algClosed hL K P (m ^ 2) hK2 ze hze
  obtain ⟨v, hv⟩ := ThetaPtDet.exists_thetaPt_of_level hL K P hg m hm hK lev
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let v' : (Fin (2 * g) → ZMod (m ^ 2)) → K := fun a => e.hom.hom (v a)
  have hvv : v = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => (e.hom_inv_id_apply (v a)).symm
  rw [hvv] at hv
  obtain ⟨th, hth, hthG⟩ :=
    exists_gen_thG_of_isThetaPt K P rig hrig m _ (levelPoint lev hg) v' (ThetaPtDet.levelPoint_pow lev hg) hv
  obtain ⟨θ, pt, hgen, hinj, hG, hall⟩ := hc
  have hβ : ∀ a, ∃ b, pt b = levelPoint lev hg a := fun a => by
    let u : Over.mk (spMap (RingHom.id K) ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap (RingHom.id K)) rfl
    obtain ⟨b, hb⟩ := hall K (RingHom.id K) (u ≫ levelPoint lev hg a) (by
      rw [← MonObj.comp_pow, ThetaPtDet.levelPoint_pow, MonObj.comp_one])
    exact ⟨b, TorsionFieldExt.comp_injective u _ (Over.OverMorphism.ext hb.symm)⟩
  choose β hβ using hβ
  refine ⟨lev, β, fun mu hmu => ?_⟩
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast e.inv.hom]
    exact (IsUnit.mk0 _ hK2).map _
  obtain ⟨s, hs⟩ := hth θ
  have e₁ : SecM.ofSec P.A θ = s • SecM.ofSec P.A th := Subtype.ext (funext hs)
  obtain ⟨r, hr⟩ := hgen th
  have e₂ : SecM.ofSec P.A th = r • SecM.ofSec P.A θ := Subtype.ext (funext hr)
  have k₁ : ∀ a, c (β a) = e.hom.hom s * v' a := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun q₁ (ThG.smul P.isLB e₁ (hthG a)))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  have k₂ : ∀ a, v' a = e.hom.hom r * c (β a) := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun (hthG a) (ThG.smul P.isLB e₂ q₁))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  by_cases hs₀ : e.hom.hom s = 0
  · have h0 : ∀ a, c (β a) = 0 := fun a => by rw [k₁, hs₀, zero_mul]
    have : (fun a => GlobalTheory.ZH.fn (mu * c (β a))) = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => by
      rw [k₂, h0, mul_zero, mul_zero]
    rw [this]
    exact hv
  · refine GenericObject.isThetaPt_unit_mul P m (levelPoint lev hg) _ _ (e.inv.hom (mu * e.hom.hom s))
      ((IsUnit.mk0 _ (mul_ne_zero hmu hs₀)).map _) (fun a => ?_) hv
    rw [k₁, ← _root_.mul_assoc]
    exact map_mul e.inv.hom _ _

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisLiftModelVectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_lift_model_vectors : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  first | exact @GlobalTheory.LieLift.main | exact GlobalTheory.LieLift.main | (intros; apply GlobalTheory.LieLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fieldPoint_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem Emb.exists_lift_fieldExt (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S)
    (hν : ν ≫ PSpace.str R E.N = s ≫ π)
    (hg : ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme),
      q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  obtain ⟨g, hg, w, hw⟩ := hg
  obtain ⟨y, hy⟩ := (Emb.range_closed R S π G' E).1 g hg
  have hsub : ∀ a b : Sp Ω, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum Ω) a b
  have hx : ∀ v, (s ≫ π) v = closedPoint R := by
    intro v
    rw [hsub v w, ← hν, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, E.f_over]
    simpa only [Scheme.Hom.comp_apply] using hg
  obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (s ≫ π) hx
  have := E.imm
  obtain ⟨y₀, hy₀⟩ := fieldPoint_lift_of_isPreimmersion E.j ν y (by rw [hsub (closedPoint Ω) w, hw, hy])
  have hcl : IsClosedImmersion (spMap (residue R)) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))
  have hY : y₀ ≫ E.Y.hom = spMap κ := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, ← Category.assoc, hy₀, hν, hκ,
      ← Spec.map_comp]
    rfl
  obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω s κ hκ
  let t : Sp Ω' ⟶ pullback E.Y.hom (spMap (io.comp κ)) :=
    pullback.lift (spMap io ≫ y₀) (𝟙 _) (by rw [Category.assoc, hY, Category.id_comp, ← Spec.map_comp]; rfl)
  have h1 : t ≫ pullback.fst _ _ = spMap io ≫ y₀ := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw' : e.inv.left ≫ pullback.snd G'.hom (spMap io ≫ s) = pullback.snd E.Y.hom (spMap (io.comp κ)) :=
    Over.w e.inv
  refine ⟨Ω', inferInstance, io, t ≫ e.inv.left ≫ l, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hl2, ← Category.assoc e.inv.left, he, ← hy₀, ← Category.assoc (spMap io), ← h1]
    simp
  · rw [Category.assoc, Category.assoc, ← Category.assoc l, hl1]
    erw [pullback.condition, ← Category.assoc e.inv.left, hw', ← Category.assoc, h2, Category.id_comp]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator : ∀ {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ), L.IsLB → A.IsLB → ∀ (u : LB.Iso A (LB.LinComb L φ₀ ε₀)), u.IsGen → ∀ (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))), c.IsGen → ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J → gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  first | exact @GlobalTheory.LinCombComp.exists_iso_comp_val | exact GlobalTheory.LinCombComp.exists_iso_comp_val | (intros; apply GlobalTheory.LinCombComp.exists_iso_comp_val <;> assumption)
end

