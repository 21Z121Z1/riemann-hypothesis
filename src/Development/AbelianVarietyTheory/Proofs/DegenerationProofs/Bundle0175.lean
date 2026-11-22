import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.EndoExtend

open GlobalTheory.CechPic

theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h₁ : CechPic.pull e a = CechPic.pull e b)
    (h₂ : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) : a = b := by
  rw [← sub_eq_zero, ← map_sub] at h₁ h₂
  rw [← sub_eq_zero]
  obtain ⟨N, hN, hc⟩ := cls_surj (a - b)
  rw [← hc] at h₁ h₂ ⊢
  exact (cls_eq_zero_iff hN).2 (GenericExtend.exists_isGen_of_densePart X U j hn ‹_› ‹_› ‹_› ‹_› P e N he ‹_› ‹_› hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₂))

section Cube

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • CechPic.pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls G x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (u : T' ⟶ T)
    (h : ∀ i, x' i = u ≫ x i) (c : Pic G.left) : CechPic.pull u.left (cubeCls G x c) = cubeCls G x' c := by
  obtain rfl : x' = fun i => u ≫ x i := funext h
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • CechPic.pull z.left c) (psum_hom (preHom u) x I.down)

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : CechPic.pull (eSec G) c = 0) :
    cubeCls G (fun _ : Fin n => (η[G] : 𝟙_ (Over S) ⟶ G)) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have : psum G (fun _ : Fin n => (1 : 𝟙_ (Over S) ⟶ G)) I.down = 1 := by
    unfold psum
    induction (List.finRange n).filter (· ∈ I.down) with
    | nil => rfl
    | cons k l ih => exact (_root_.one_mul _).trans ih
  rw [e₁] at this
  rw [this]
  exact (congrArg (_ • ·) hc).trans (smul_zero _)

variable {G} in
theorem push_cubeCls {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : T'.left ⟶ T.left) (hu : u ≫ T.hom = T'.hom ≫ f)
    (hx : ∀ i, (x' i).left ≫ φ = u ≫ (x i).left) (c : Pic G.left) :
    CechPic.pull u (cubeCls G x c) = cubeCls G' x' (CechPic.pull φ c) := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp,
    psum_push h x' x (Over.homMk u hu) (fun i => Over.OverMorphism.ext (hx i)) I.down]
  rfl

end Cube

theorem hypS_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over X) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G)
    (hext : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback j).map F = f)
    (h : HypS ((Over.pullback j).obj G) (L.L.pull (pullback.fst G.hom j))) : HypS G L.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := h
  obtain ⟨w, ⟨hw, rfl⟩, -⟩ := hext w' hw'
  obtain ⟨wd, ⟨hwd, rfl⟩, -⟩ := hext wd' hwd'
  have hL := L.isLB
  have hL' := pull_isLB hL (pullback.fst G.hom j)
  have hG := isGrpPullback_pullback G j
  have A : ∀ {Y Z : Over X} (a : Y ⟶ Z),
      ((Over.pullback j).map a).left ≫ pullback.fst Z.hom j = pullback.fst Y.hom j ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  have h0 : CechPic.pull (eSec G) (cls L.L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨L.rig, L.rigGen⟩
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · refine (hext (𝟙 _) inferInstance).unique ⟨Serre.isMonHom_mul w wd, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_mul, hs]
  · refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cubeLB G _ hL).symm)
    refine pic_ext j hn G (eSec G) (Over.w η[G]) (h0.trans ?_) ?_
    · refine ((pull_cubeCls G _ (fun _ => η[G]) η[G] (fun i => ?_) _).trans (cubeCls_one G _ h0)).symm
      fin_cases i <;> simp
    · have e := ((cls_eq_iff hL' (LB.isLB_linComb hL' _ _)).2 hp).trans (cls_cubeLB ((Over.pullback j).obj G) _ hL')
      have e' := push_cubeCls hG (T' := (Over.pullback j).obj G) (T := G) ![𝟙 _, (Over.pullback j).map w] ![𝟙 G, w]
        (pullback.fst G.hom j) pullback.condition (fun i => by
          fin_cases i
          · simp
          · exact A w) (cls L.L hL)
      exact e.trans e'.symm
  · refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
    refine pic_ext j hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
    · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
        (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
      fin_cases i <;> simp
    · let δ := lift ((Over.pullback j).map (fst G G)) ((Over.pullback j).map (snd G G))
      have e := congrArg (CechPic.pull δ.left) ((cls_cubeLB ((Over.pullback j).obj G) _ hL').symm.trans
        (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 ha).trans
          (cls_cubeLB ((Over.pullback j).obj G) _ hL')))
      have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hG (T' := (Over.pullback j).obj (G ⊗ G)) (T := G ⊗ G)
        (fun i => (Over.pullback j).map (x i)) x (pullback.fst (G ⊗ G).hom j) pullback.condition (fun i => A _)
        (cls L.L hL)
      rw [pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G ≫ w, snd G G] i)) δ
          (fun i => by fin_cases i <;> simp [δ]),
        pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G, snd G G ≫ wd] i)) δ
          (fun i => by fin_cases i <;> simp [δ])] at e
      exact (e' _).trans (e.trans (e' _).symm)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isIso_stalkClosedPointTo : IsIso (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) := by
  have e : M.stalkHom (M.pt (IsLocalRing.closedPoint Ω)) =
      (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom := by
    unfold RatModel.stalkHom
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom
  rw [← e]
  refine ⟨M.stalkHom_injective _, fun x => ?_⟩
  have hx : x ∈ M.O (M.pt (IsLocalRing.closedPoint Ω)) := by
    have h := M.O_genericPoint
    rw [← M.pt_apply (IsLocalRing.closedPoint Ω)] at h
    exact h.ge trivial
  obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem isPreimmersion_pt : IsPreimmersion M.pt := by
  have := isIso_stalkClosedPointTo M
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

theorem flat_pt : Flat M.pt := by
  have := isIso_stalkClosedPointTo M
  have := GenericExt.flat_fromSpecStalk M.Z (M.pt (IsLocalRing.closedPoint Ω))
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

end Model

theorem hypS_and_endo_and_iso_extend : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  intro hdvr o Ω _ _ _ hA S ρ M U₀ Q hO
  have := hA.ded
  have := hA.ft
  have := hA.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hX : Geo.Tor.IsNormalScheme M.Z ∧ ∃ z : M.Z ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z :=
    ⟨hO.normal, _, MinorModel.locallyOfFiniteType_int M, MinorModel.flat_int M _⟩
  have := isPreimmersion_pt M
  have := flat_pt M
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have hL := Q.L.isLB
  refine ⟨?_, GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ M.pt hX ‹_› ‹_› inferInstance inferInstance _ _ Q.semi Q.semi, ?_⟩
  · have : Nonempty U₀ := hO.ne.to_subtype
    have : IsDominant U₀.ι := ⟨by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact U₀.isOpen.dense hO.ne⟩
    have := ρ.P.isAb.comm
    refine hypS_of_densePart U₀.ι hO.normal Q.G Q.L (GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ U₀.ι hX inferInstance inferInstance
      inferInstance inferInstance _ _ Q.semi Q.semi) ?_
    have hP := ρ.P.isLB
    have h₁ : HypS ((Over.pullback Q.u₀).obj ρ.P.A) (Q.L.L.pull Q.φ) :=
      SymBaseChange.hypS_baseChange _ _ ρ.P.A ((Over.pullback Q.u₀).obj ρ.P.A) Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) _ _ hP (pull_isLB hL _)
        (isGrpPullback_pullback _ _) ⟨Q.w, Q.w_gen⟩ ρ.hypS
    let ψ := Q.cart.1.lift (pullback.fst Q.G.hom U₀.ι) (pullback.snd _ _) pullback.condition
    have hψ : ψ ≫ Q.φ = pullback.fst Q.G.hom U₀.ι := Q.cart.1.lift_fst _ _ _
    refine SymBaseChange.hypS_baseChange _ _ ((Over.pullback Q.u₀).obj ρ.P.A) ((Over.pullback U₀.ι).obj Q.G) (𝟙 _) ψ _ _ (pull_isLB hL _) (pull_isLB hL _)
      (Q.cart.cancel ((isGrpPullback_pullback Q.G U₀.ι).congr (Category.id_comp _).symm hψ.symm)
        ((Q.cart.1.lift_snd _ _ _).trans (Category.comp_id _).symm)) ?_ h₁
    refine (cls_eq_iff (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    exact (congrArg (CechPic.pull · (cls _ hL)) hψ.symm).trans (pull_comp ψ Q.φ (cls _ hL))
  · intro n x x' hx ε ε' _ _ h
    have := smooth_tensorObj_hom Q.G Q.G
    have := geometricallyIntegral_tensorObj_hom Q.G Q.G
    have h0 : CechPic.pull (eSec Q.G) (cls Q.L.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨Q.L.rig, Q.L.rigGen⟩
    have key : ∀ (y : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)) (δ : Fin n → ℤ), (∀ i, IsMonHom (y i)) →
        CechPic.pull (η[Q.G ⊗ Q.G]).left (cls _ (LB.isLB_linComb hL (fun i => (y i).left) δ)) = 0 := by
      intro y δ hy
      rw [cls_linComb hL, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, ← pull_comp, ← Over.comp_left, (hy i).one_hom]
      exact (congrArg (_ • ·) h0).trans (smul_zero _)
    refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      (pic_ext M.pt hO.normal (Q.G ⊗ Q.G) (η[Q.G ⊗ Q.G]).left (Over.w _)
        ((key x ε fun i => (hx i).1).trans (key x' ε' fun i => (hx i).2).symm) ?_)
    exact (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2 h

end GlobalTheory.ZH.EndoExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.GBasis

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Y' ⟶ Y) (φ₁ : K → (Y' ⟶ X)) (hφ : ∀ a, φ₁ a = h ≫ φ a) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s₁ : LB.Sec (LB.LinComb L φ₁ ε), ∀ (z : Y') J, Good L z J → sval s₁ (𝟙 _) z J = sval s h z J := by
  obtain rfl : φ₁ = fun a => h ≫ φ a := funext hφ
  exact ⟨_, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_lin_one {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)
    (b : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s, Lin G L N h (fun _ : Fin 1 => b) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_pull (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ))
    (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left)
    (fun _ => by rw [← Over.comp_left, whiskerRight_snd]) b
  refine ⟨s, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul]

theorem fnR_surj {R : Type} [CommRing R] {n : ℕ} (c : Fin n → Γ(Sp R, ⊤)) : ∃ a : Fin n → R, c = fun i => fnR (a i) :=
  ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i), funext fun i => by
    simp [fnR]⟩

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem liftFun_one (W) : liftFun A.A (T := TFK (R := R) F) W ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 1) = 1 := by
  simp only [liftFun, map_one]

theorem eq_of_cmb_one {b t : SecA A F k} (h : Cmb (fun _ : Fin 1 => b) (fun _ => 1) t) : t = b :=
  SecOps.sec_ext fun j => by rw [h j, Fin.sum_univ_one, liftFun_one, _root_.one_mul]

theorem exists_cmb : ∀ {n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F), ∃ t, Cmb b a t
  | 0, _, _ => ⟨SecOps.secZero, fun j => by rw [Fin.sum_univ_zero]; rfl⟩
  | n + 1, b, a => by
    obtain ⟨t, ht⟩ := exists_cmb (fun i => b i.succ) (fun i => a i.succ)
    refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a 0))) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]; rfl

variable {M : Type} [AddCommGroup M] [Module F M] {E : SecA A F k → M → Prop}

theorem cmb_rel (hex : ∀ t, ∃ s, E t s)
    (hl : ∀ (t t' t'' : SecA A F k) (s s' : M) (c : F), E t s → E t' s' →
      (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) →
      E t'' (c • s + s')) :
    ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → M) (a : Fin n → F) (t : SecA A F k), (∀ i, E (b i) (s i)) →
      Cmb b a t → E t (∑ i, a i • s i)
  | 0, _, _, _, t, _, h => by
    obtain ⟨s, hs⟩ := hex t
    have := hl t t t s s (-1) hs hs (fun j => by rw [h j, Fin.sum_univ_zero, mul_zero, add_zero])
    rw [neg_one_smul, neg_add_cancel] at this
    rwa [Fin.sum_univ_zero]
  | n + 1, b, s, a, t, hb, h => by
    obtain ⟨t', ht'⟩ := exists_cmb (fun i => b i.succ) (fun i => a i.succ)
    have ih := cmb_rel hex hl _ (fun i => s i.succ) _ t' (fun i => hb i.succ) ht'
    rw [Fin.sum_univ_succ]
    exact hl (b 0) t' t _ _ (a 0) (hb 0) ih fun j => by rw [h j, Fin.sum_univ_succ, ht' j]

end Av

theorem card_eq_of_bases {F M : Type} [Field F] [AddCommGroup M] [Module F M] {n m : ℕ} {s : Fin n → M}
    {s' : Fin m → M} (h : ∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) (h' : ∀ x, ∃! a : Fin m → F, x = ∑ i, a i • s' i) :
    n = m := by
  have key : ∀ {n : ℕ} {s : Fin n → M}, (∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) →
      Nonempty ((Fin n → F) ≃ₗ[F] M) := fun {n s} h =>
    ⟨LinearEquiv.ofBijective (Fintype.linearCombination F s) ⟨fun a b e => (h _).unique
      (Fintype.linearCombination_apply F s a) (e.trans (Fintype.linearCombination_apply F s b)), fun x => by
        obtain ⟨a, ha, -⟩ := h x
        exact ⟨a, (Fintype.linearCombination_apply F s a).trans ha.symm⟩⟩⟩
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  simpa using (e.trans e'.symm).finrank_eq

theorem val_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (c : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · simp [hc]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have h : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ) :=
      ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, _root_.mul_comm]⟩
    rw [hv _ _ h]
    exact_mod_cast (Nat.cast_nonneg n : (0 : ℚ) ≤ n)

theorem prim_of {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {r mu : ℕ}
    {cls : Fin r → D.toPre.X} {s : Fin r → Fam D.toPre F 1} (hA : Adapted 1 Q cls mu) (hN : Norms D Q v 1 cls s)
    {c d : Fin r → F} (hc : ∀ i, 0 ≤ v (c i)) (hd : ∀ i, 0 ≤ v (d i)) (hs : ∀ i, s i = d i • ∑ j, c j • s j) :
    Prim D Q v (∑ j, c j • s j) := by
  classical
  have h0 : ∀ i, Q (cls i) = 0 := fun i => by
    have a := hA.1 i (-cls i)
    rw [one_smul, add_neg_cancel, QForm.Q_zero hϖ D hQ] at a
    by_cases e : cls i = 0
    · rw [e, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ e
      omega
  have hn : ∀ q : ℚ, NuGe D Q F v 1 (∑ j, c j • s j) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (c i) := fun q => by
    rw [(hN.2 c q).1]
    simp only [h0, Int.cast_zero, zero_div, add_zero]
  refine ⟨(hn 0).2 hc, fun q hq H => ?_⟩
  obtain ⟨i, -⟩ := hA.2.2.1 0
  have e : (Pi.single i 1 : Fin r → F) = fun j => d i * c j := (hN.1 (s i)).unique
    (by simp [Pi.single_apply]) (by rw [hs i, Finset.smul_sum]; simp only [mul_smul])
  have e₁ : (1 : F) = d i * c i := by simpa using congrFun e i
  have e₂ : v (d i) + v (c i) = 0 := by rw [← v.map_mul, ← e₁, v.map_one]
  have e₃ : (q : WithTop ℚ) ≤ 0 := by
    calc (q : WithTop ℚ) = 0 + q := (zero_add _).symm
      _ ≤ v (d i) + v (c i) := add_le_add (hd i) ((hn q).1 H i)
      _ = 0 := e₂
  have : q ≤ 0 := by exact_mod_cast e₃
  linarith

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (gam : K →+* FractionRing V) (h : spMap gam ≫ x = jK V ≫ χ) (θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))), FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ) → ∀ (k r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), 1 ≤ k → AllBasis G₀ L₀ k x τ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U.toUnifPre) (th : SecA A F 1) (ϑ : Fam D.toPre F 1) (cls : Fin r → D.toPre.X) (mu : ℕ) (b τF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k) (B : Matrix (Fin r) (Fin r) (FractionRing V)), RigPull A.A G₀ (jK V ≫ χ) φ w ρ ρ₀ ∧ NormW U.toUnifPre w₀ ρ ∧ U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ Thru w 1 (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) θ th ∧ (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) (τ i) (τF i)) ∧ Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ (∀ i, U.ExpandsF F k w₀ (b i) (s i)) ∧ (∀ t, ∃! a, Cmb τF a t) ∧ (∀ i, Cmb τF (B.map (algebraMap (FractionRing V) F) i) (b i)) ∧ BasisBy G₀ L₀ k x gam χ h τ B := by
  intro hLL h1 h2 h3 h4 V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U Z G₀ _ L₀ hL₀ ρ₀ χ Φ ω hRP K _ x gam h θ
    hFr k r τ hk hτ
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨hbij, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hB D A G hG U
  obtain ⟨φ, w, ρ, w₀, hR, hW, hbr⟩ := GlobalTheory.OneBasis.Bridge.exists_bridge Z G₀ L₀ hL₀ ρ₀ V _ D A G U.toUnifPre χ Φ ω hRP
  have cal := GlobalTheory.OneBasis.Calc.main Z G₀ L₀ hL₀ V (jK V ≫ χ) A φ w hR.1 hR.2.1 F
  have lev : ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ)
      (b : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ))) (bF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k),
      BasisAlong G₀ L₀ k (𝟙 _) b ∧
      (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) ∧
      Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ ∀ i, U.ExpandsF F k w₀ (bF i) (s i) := fun k hk => by
    obtain ⟨r, cls, mu, f, hf, hs⟩ := GlobalTheory.OneBasis.AdaptedFamily.main hLL V ϖ hϖ D Q hQ k hk
    choose s hs using hs F
    obtain ⟨σ, hσ, hσb⟩ := GlobalTheory.OneBasis.ModelBasis.main hLL V D Q A G U k hk r cls mu f hf
    obtain ⟨b, hb, hb'⟩ := hbr k r σ hσb
    choose bF hbF using fun i => ((cal k).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b i)).exists
    exact ⟨r, cls, mu, b, bF, s, hb, hbF, hf.1,
      GlobalTheory.OneBasis.NormsPf.norms_of_adapted hLL h1 h2 h3 h4 V hc ϖ hϖ D Q hQ F v hv k hk r cls mu f s hf hs,
      fun i => hb' i F (f i) (s i) (bF i) (hσ i) (hs i) (hbF i)⟩
  have down : ∀ (k : ℕ) (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk (jK V ≫ χ)))), ∃ t : SecA A F k,
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t :=
    fun k s => ((cal k).1 (Over.mk (jK V ≫ χ)) (jFK (R := V) F) rfl s).exists
  have one : ∀ (k : ℕ) (T : Over Z) (g : Over.mk (jK V ≫ χ) ⟶ T) b s (bF t : SecA A F k),
      Lin G₀ L₀ k g (fun _ : Fin 1 => b) (fun _ => 1) s →
      Thru w k (T' := TFK (R := V) F) (spMap (algebraMap (FractionRing V) F) ≫ g.left) b bF →
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t →
      t = bF := fun k T g b s bF t a₁ a₂ a₃ => by
    have := (cal k).2.1 (FractionRing V) (jK V ≫ χ) T g (algebraMap (FractionRing V) F) rfl 1 (fun _ => b)
      (fun _ => 1) s (fun _ => bF) t (by simpa only [fnR, map_one] using a₁) (fun _ => a₂) a₃
    simp only [map_one] at this
    exact eq_of_cmb_one this
  have rel : ∀ (k : ℕ), 1 ≤ k → ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → Fam D.toPre F k) (a : Fin n → F)
      (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (b i) (s i)) → Cmb b a t → U.ExpandsF F k w₀ t (∑ i, a i • s i) :=
    fun k hk => cmb_rel (fun t => ((hbij F k hk w₀ hW.1).1 t).exists) (hlin F k w₀)
  have hx : (jFK (R := V) F ≫ spMap gam) ≫ x = jFK (R := V) F ≫ jK V ≫ χ := by rw [Category.assoc, h]

  obtain ⟨th, hth⟩ := ((cal 1).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx θ).exists
  obtain ⟨ϑ, hϑ, hP⟩ : ∃ ϑ, U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ := by
    obtain ⟨r₁, cls₁, mu₁, b₁, bF₁, s₁, hb₁, ht₁, hA₁, hN₁, hE₁⟩ := lev 1 le_rfl
    obtain ⟨b', hb', H⟩ := hFr
    obtain ⟨s₀, l₁, l₂⟩ := H 0
    obtain ⟨t₀, ht₀⟩ := down 1 s₀
    obtain ⟨bF', hbF'⟩ :=
      ((cal 1).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b' 0)).exists
    have e₁ := one 1 _ _ _ _ th t₀ l₁ hth ht₀
    have e₂ := one 1 _ _ _ _ bF' t₀ l₂ hbF' ht₀
    obtain rfl : bF' = th := e₂.symm.trans e₁
    let ga : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
    have hga : spMap ga = jFK (R := V) F ≫ jK V := Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
    have cm : ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk χ))) (bF : Fin n → SecA A F 1) s t,
        BasisAlong G₀ L₀ 1 (𝟙 _) b →
        (∀ i, Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) →
        Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) s t →
        ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ Cmb bF c t := fun n b bF s t a₁ a₂ a₃ => by
      obtain ⟨c, hc⟩ := (a₁ s).exists
      obtain ⟨c, rfl⟩ := fnR_surj c
      rw [← hga] at a₂ a₃
      refine ⟨fun i => ga (c i), fun i => val_nonneg hϖ hv (c i), (cal 1).2.1 V χ (Over.mk χ) (𝟙 _) ga
        (by rw [hga, Category.assoc]) n b c s bF t hc (fun i => ?_) a₃⟩
      have e : spMap ga ≫ (𝟙 (Over.mk χ) : _ ⟶ _).left = spMap ga := Category.comp_id _
      rw [e]
      exact a₂ i
    obtain ⟨c, hc₀, hc₁⟩ := cm _ b₁ bF₁ _ _ hb₁ ht₁ hbF'
    have hE := rel 1 le_rfl bF₁ s₁ c _ hE₁ hc₁
    choose d hd₀ hd₁ using fun i => cm 1 b' (fun _ => bF') _ _ hb'
      (fun j => by rw [Subsingleton.elim j 0]; exact hbF') (ht₁ i)
    refine ⟨_, hE, prim_of hϖ hQ hA₁ hN₁ (d := fun i => d i 0) hc₀ (fun i => hd₀ i 0) fun i => ?_⟩
    have := rel 1 le_rfl (fun _ : Fin 1 => bF') (fun _ => _) (d i) _ (fun _ => hE) (hd₁ i)
    rw [Fin.sum_univ_one] at this
    exact ((hbij F 1 le_rfl w₀ hW.1).1 _).unique (hE₁ i) this

  obtain ⟨r', cls, mu, b, bF, s, hb, ht, hA, hN, hE⟩ := lev k hk
  choose τF hτF using fun i => ((cal k).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx (τ i)).exists
  have hg : spMap ((algebraMap (FractionRing V) F).comp gam) = jFK (R := V) F ≫ spMap gam :=
    Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hbas : ∀ t : SecA A F k, ∃! a, Cmb τF a t :=
    (cal k).2.2 K x ((algebraMap (FractionRing V) F).comp gam) (by rw [hg, hx]) r τ τF hτ (by rw [hg]; exact hτF)
  obtain rfl : r' = r := by
    choose s' hs' using fun i => ((hbij F k hk w₀ hW.1).1 (τF i)).exists
    refine card_eq_of_bases hN.1 (s' := s') fun y => ?_
    obtain ⟨t, ht, hu⟩ := (hbij F k hk w₀ hW.1).2 y
    obtain ⟨a, ha, hau⟩ := hbas t
    refine ⟨a, ((hbij F k hk w₀ hW.1).1 t).unique ht (rel k hk τF s' a t hs' ha), fun a' ha' => hau a' ?_⟩
    obtain ⟨t', ht'⟩ := exists_cmb τF a'
    have := rel k hk τF s' a' t' hs' ht'
    rw [← ha'] at this
    rw [← hu t' this]
    exact ht'
  choose g hg using fun i => exists_lin_one G₀ L₀ k
    (Over.homMk (jK V) rfl : Over.mk (jK V ≫ χ) ⟶ Over.mk χ) (b i)
  have hBi : ∀ i, ∃ c : Fin r' → FractionRing V,
      Lin G₀ L₀ k (Over.homMk (spMap gam) h : Over.mk (jK V ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (c j)) (g i) := fun i => by
    obtain ⟨c, hc⟩ := (hτ (FractionRing V) gam (jK V ≫ χ) h (g i)).exists
    obtain ⟨c, rfl⟩ := fnR_surj c
    exact ⟨c, hc⟩
  choose B hBB using hBi
  refine ⟨φ, w, ρ, w₀, th, ϑ, cls, mu, bF, τF, s, Matrix.of B, hR, hW, hϑ, hP, hth, hτF, hA, hN, hE, hbas, fun i => ?_,
    b, hb, fun i => ⟨g i, hBB i, hg i⟩⟩
  obtain ⟨t, ht'⟩ := down k (g i)
  rw [← one k _ _ _ _ (bF i) t (hg i) (ht i) ht']
  exact (cal k).2.1 (FractionRing V) (jK V ≫ χ) (Over.mk x) _ (algebraMap (FractionRing V) F) rfl r' τ (B i) (g i) τF t
    (hBB i) hτF ht'

end GlobalTheory.GBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  first | exact @GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | exact GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | (intros; apply GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_specialisation_of_mem_closure_thetaPoints : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (m : ℕ) (ρ z : K) (v : D.La → K), Odd m → Compat H (m ^ 2) z ρ → v ≠ 0 → (∀ G, VanishC D m G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (i : K →+* κ) (o : Full D C) (_ : Mdl o) (v' : D.La → S) (r' z' : S), (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) ∧ (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧ o.Theta m (fun x => v' x) ∧ (∀ x, res (v' x) = i (v x)) ∧ (r' : C) = o.ρ ∧ res r' = i ρ ∧ (z' : C) = o.I.ζ (m ^ 2) ∧ res z' = i z := by
  first | exact @GlobalTheory.ThetaClosure.exists_trait | exact GlobalTheory.ThetaClosure.exists_trait | (intros; apply GlobalTheory.ThetaClosure.exists_trait <;> assumption)
end

