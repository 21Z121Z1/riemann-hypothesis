import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDivisorOfForm
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isDivOfForm_and_toPic : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  intro k _ _ Y _ _ q n _ η hη
  obtain ⟨c, hc⟩ := (isFreeGen_baseForm q n).2 η
  replace hc : c • baseForm q n = η := hc
  have h0 : c ≠ 0 := fun e => hη (by rw [← hc, e, zero_smul])
  have h := (isDivOfForm_canonical q n).smul (Units.mk0 c h0)
  rw [Units.val_mk0, hc] at h
  refine ⟨⟨_, h⟩, fun K hK Kc => ?_⟩
  rw [hK.unique hη h, map_add, toPic_principal]
  simpa using (presents_canonical q n).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ Kc))

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmul
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

section Basic

variable {X : Over (Sp R)} (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (r : R)

theorem fv_add_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (f + f') D D' φ x = fv f D D' φ x + fv f' D D' φ x := rfl

theorem fv_smul_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (r • f) D D' φ x = r • fv f D D' φ x := rfl

theorem cotVal_add_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (f + f') y = cotVal f y + cotVal f' y := by
  unfold cotVal
  simp only [fv_add_apply, map_add, map_sub]
  abel

theorem cotVal_smul_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (r • f) y = r • cotVal f y := by
  unfold cotVal
  simp only [fv_smul_apply, map_smul, map_sub, smul_sub]

end Basic

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} {t : G.TorsionTower A} {c c' : primDR A}

def Dat.sum (d : Dat t c) (d' : Dat t c') : Dat t (c + c') where
  f := d.f + d'.f
  cl := by rw [map_add, d.cl, d'.cl]; rfl
  g := fun D _ _ x y ↦ d.g D x y + d'.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    have h' := d'.add D D' φ x y
    simp only [fv_add_apply, map_add]
    linear_combination h + h'
  h := fun n ↦ d.h n + d'.h n
  res := fun n ↦ by
    have h := d.res n
    have h' := d'.res n
    simp only [fv_add_apply, map_add]
    linear_combination h + h'

def Dat.scale (r : R) (d : Dat t c) : Dat t (r • c) where
  f := r • d.f
  cl := by rw [map_smul, d.cl]; rfl
  g := fun D _ _ x y ↦ r • d.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h, smul_sub, smul_sub]
  h := fun n ↦ r • d.h n
  res := fun n ↦ by
    have h := d.res n
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h]

theorem Dat.coc_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').coc n = d.coc n + d'.coc n := by
  simp only [Dat.coc, Dat.sum, fv_add_apply, map_add]
  abel

theorem Dat.om_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').om n = d.om n + d'.om n := by
  simp only [Dat.om, Dat.sum, cotVal_add_apply, map_add]
  abel

theorem Dat.coc_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).coc n = r • d.coc n := by
  simp only [Dat.coc, Dat.scale, fv_smul_apply, map_smul, smul_sub]

theorem Dat.om_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).om n = r • d.om n := by
  simp only [Dat.om, Dat.scale, cotVal_smul_apply, map_smul, smul_sub]

theorem isCan_add_smul (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt), IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧
      ∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x) := by
  constructor
  · rintro c c' _ _ ⟨d, z, w, hz, hw, rfl⟩ ⟨d', z', w', hz', hw', rfl⟩
    refine ⟨d.sum d', z + z', w + w', fun n ↦ ?_, fun n ↦ ?_, (map_add G.rigMk _ _).symm⟩
    · rw [Dat.coc_sum, ← hz, ← hz']; rfl
    · rw [Dat.om_sum, ← hw, ← hw']; rfl
  · rintro r c _ ⟨d, z, w, hz, hw, rfl⟩
    refine ⟨d.scale r, r • z, r • w, fun n ↦ ?_, fun n ↦ ?_, (map_smul G.rigMk r (z, w)).symm⟩
    · rw [Dat.coc_scale, ← hz]; rfl
    · rw [Dat.om_scale, ← hw]; rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QDivSum

theorem sum_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro D E a b ha hb hD hE
  refine ⟨(BoundaryFibre.eff_nsmul hD b).add (BoundaryFibre.eff_nsmul hE a), ?_, ?_⟩
  · funext z
    simp only [qWeil, Pi.add_apply, CartierDiv.mult_add, SmallSecHeight.mult_nsmul]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  · intro C hC
    have e : cls (toLB (b • D + a • E)) (isLB_toLB _) = b • cls (toLB D) (isLB_toLB D) + a • cls (toLB E) (isLB_toLB E) := by
      rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul]
    rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) b a C hC e]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp

end GlobalTheory.QDivSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem unitAt_functionFieldMap_of_unitAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.UnitAt (s y) f) :
    _root_.GlobalTheory.Cartier.UnitAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, hunit, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, hunit.map _, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem regAt_functionFieldMap_of_regAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.RegAt (s y) f) :
    _root_.GlobalTheory.Cartier.RegAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in

theorem _root_.GlobalTheory.Discrepancy.pullCart_supp_and_eff : ∀ (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : _root_.GlobalTheory.Cartier.CartierDiv X),
    (∀ y : Y, y ∈ (_root_.GlobalTheory.Discrepancy.pullCart s D).supp →
      s y ∈ D.supp) ∧
    (D.Eff → (_root_.GlobalTheory.Discrepancy.pullCart s D).Eff) := by
  intro X Y _ _ s _ D
  refine ⟨fun y hy => ?_, fun hD => ?_⟩
  · obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hg' := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    rw [hg'.mem_supp_iff] at hy
    rw [hg.mem_supp_iff]
    intro hunit
    exact hy (unitAt_functionFieldMap_of_unitAt s hunit)
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff] at hD ⊢
    intro y g' hg'
    obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hpull := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    have hquot := (hpull.iff_unitAt).1 hg'
    have hreg : _root_.GlobalTheory.Cartier.RegAt y
        ((_root_.GlobalTheory.Discrepancy.fnPull s g : (Y.functionField)ˣ) : Y.functionField) :=
      regAt_functionFieldMap_of_regAt s (hD (s y) g hg)
    have hprod := hquot.regAt.mul hreg
    rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at hprod

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinementStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hyper_cohomology_cover_refinement : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  first | exact @GlobalTheory.CechDR.restrict_cover_affine_bijective | exact GlobalTheory.CechDR.restrict_cover_affine_bijective | (intros; apply GlobalTheory.CechDR.restrict_cover_affine_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTrivialPullbackOfIsPullbackGeneratorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechTrivial_pullback_of_isPullbackGenerator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  first | exact @GlobalTheory.CharKer.triv_pull_of_isPullGen | exact GlobalTheory.CharKer.triv_pull_of_isPullGen | (intros; apply GlobalTheory.CharKer.triv_pull_of_isPullGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterEqOneOfDescendedLineBundleTrivialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_eq_one_of_descended_lineBundle_trivial : ∀ (K : Type) [Field K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsMonHom q → IsPullback i (toUnit N) q η[A'] → M.IsLB → IsEquivGen i q χ M e → Triv M → χ = 1 := by
  first | exact @GlobalTheory.CharKer.character_eq_one_of_triv | exact GlobalTheory.CharKer.character_eq_one_of_triv | (intros; apply GlobalTheory.CharKer.character_eq_one_of_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLawStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  first | exact @GlobalTheory.Desc.ChartLaw.chart_mulAgree | exact GlobalTheory.Desc.ChartLaw.chart_mulAgree | (intros; apply GlobalTheory.Desc.ChartLaw.chart_mulAgree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem exists_objMap_cancel_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : ∃ m₁ : ObjMap o₁ o₂ f, m₁.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

theorem classify_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  intro p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a
  have cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ := by
    intro f f' e m₀; subst e; exact ⟨m₀, rfl⟩
  have hrY : (r a).left ≫ Y.hom = Y.hom := Over.w (r a)
  obtain ⟨ma, hma⟩ := (hρ a).2.2

  have h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁],
      my.comp ma, fun c => ?_⟩
    have e₁ := hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))
    have e₂ := hma c
    simp only [sympTwist] at e₂ ⊢
    change _ ≫ my.φ ≫ ma.φ = _
    rw [← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]

  obtain ⟨mr, hmr⟩ := cast hrY.symm m
  obtain ⟨m₂, hφ⟩ := exists_objMap_cancel_φ mr m
  rw [hmr] at hφ
  have hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left := by
    intro c
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, hlv' c]
      simp only [sympTwist] at hlv' ⊢
      rw [hlv', ← Over.comp_left, hr a c]
      rfl
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc,
        Over.w (lv' c)]
      simp
  have h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt],
      m₂.comp my, fun c => ?_⟩
    change _ ≫ m₂.φ ≫ my.φ = _
    rw [← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]
  exact (hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.VertProj

theorem isProjOver_strHom_zmod : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) Z) := by
  intro k _ X p D hX Z i _ l _ _
  have : Module.Finite ℤ k := hX.finite
  have hfin : (Int.castRingHom k).Finite := (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact hfin
  have e : i ≫ p ≫ spMap (Int.castRingHom k) =
      strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by
    rw [← e]; infer_instance
  have hpr : IsProper (strHom (ZMod l) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
  have hq : IsQProjOver p := by
    obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
    exact ⟨N, j, inferInstance, inferInstance, hjp⟩
  have hq₁ := isQProjOver_comp_spMap_of_finiteType hfin.finiteType hq
  have hq₂ := isQProjOver_of_isPullback_spMap (Int.castRingHom (ZMod l))
    (IsPullback.of_hasPullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) hq₁
  let u := Limits.pullback.lift (f := p ≫ spMap (Int.castRingHom k))
    (g := spMap (Int.castRingHom (ZMod l))) i (strHom (ZMod l) Z) e
  have : IsImmersion u := by
    have : IsImmersion (u ≫ Limits.pullback.fst _ _) := by
      rw [Limits.pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp u (Limits.pullback.fst _ _)
  have hu : u ≫ Limits.pullback.snd _ _ = strHom (ZMod l) Z := Limits.pullback.lift_snd _ _ _
  rw [← hu] at hpr ⊢
  exact isProjOver_of_isProper_of_isImmersion _ hq₂

end GlobalTheory.VertProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageDiscrete
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMLatticeDiscrete

theorem cmLattice_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  obtain ⟨N, hNpos, hN⟩ := hL

  have hfin : {w : Fin n → ℂ | w ∈ Λ ∧ ‖w‖ ≤ 1}.Finite := by
    have hS := NumberField.Embeddings.finite_of_norm_le E ℂ ((N : ℝ) * 1)
    have hT : {x : E | x ∈ L ∧ ∀ i, ‖φ i x‖ ≤ 1}.Finite := by
      refine (hS.image (fun y : E ↦ y / (N : E))).subset ?_
      rintro x ⟨hxL, hxb⟩
      refine ⟨(N : E) * x, ⟨hN x hxL, fun σ ↦ ?_⟩, ?_⟩
      · obtain ⟨i, hi, -⟩ := hφ σ
        have hb : ‖σ x‖ ≤ 1 := by
          rcases hi with h | h
          · rw [h]; exact hxb i
          · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact hxb i
        rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)
      · have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
        simp only
        field_simp
    refine (hT.image (fun x : E ↦ fun j ↦ φ (e j) x)).subset ?_
    rintro w ⟨hwΛ, hwb⟩
    obtain ⟨x, hxL, rfl⟩ := (hΛ w).1 hwΛ
    refine ⟨x, ⟨hxL, fun i ↦ ?_⟩, rfl⟩
    have := norm_le_pi_norm (fun j ↦ φ (e j) x) (e.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact this.trans hwb
  apply discreteTopology_of_isOpen_singleton_zero
  set F : Set (Fin n → ℂ) := {w | w ∈ Λ ∧ ‖w‖ ≤ 1} \ {0}
  have hF : IsClosed F := (hfin.subset Set.diff_subset).isClosed
  have hU : IsOpen (Metric.ball (0 : Fin n → ℂ) 1 ∩ Fᶜ) := Metric.isOpen_ball.inter hF.isOpen_compl
  convert hU.preimage continuous_subtype_val using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, F, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  constructor
  · intro h
    have h0 : w = 0 := by simpa using congrArg Subtype.val h
    subst h0
    simp
  · rintro ⟨h1, h2⟩
    have : w = 0 := h2 ⟨hw, h1.le⟩
    exact Subtype.ext this

end GlobalTheory.CMLatticeDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_restrict_basis_extended_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X : Scheme.{0}) (s : X ⟶ Sp R₀) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (extMap R₁ (CoefMap.restrict (OAff s) G)).pull1 ∧ Function.Bijective (extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 := by
  first | exact @GlobalTheory.Obs.BasisExt.restrict_ext_bijective | exact GlobalTheory.Obs.BasisExt.restrict_ext_bijective | (intros; apply GlobalTheory.Obs.BasisExt.restrict_ext_bijective <;> assumption)
end

