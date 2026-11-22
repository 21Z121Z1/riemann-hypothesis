import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueRigMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffRing

open TrivSqZeroExt (inl inr)

theorem existsUnique_coeff_alg {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {dd : Fin n → Fld G.left}
    (hdd : ∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
      (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f))
    {C : Type} [CommRing C] [Algebra R C] (y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C ⟶ G)
    {V : G.left.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ y.left ⁻¹ᵁ V) (δ : Γ(G.left, V) → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left V h f * δ f' + evalPt y.left V h f' * δ f)
    (hbase : ∀ r, δ (constFn G.hom V r) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left V h (dd a V f) := by
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (TrivSqZeroExt.inlAlgHom R C C) ≫ y
  have hz : ⊤ ≤ z.left ⁻¹ᵁ V := fun t _ => h (Set.mem_univ _)
  have ez : ∀ s, evalPt z.left V hz s = inl (evalPt y.left V h s) := fun s =>
    evalPt_spMap_comp (TrivSqZeroExt.inlAlgHom R C C).toRingHom y.left V h hz s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.InvFieldBasis.exists_dualHom (evalPt y.left V h) δ hadd hmul
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hV ψ
  have hxp : x ≫ G.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C)).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap R (DualNumber C)) fun a => ?_).trans rfl
    rw [← evalPt_constFn G.hom x V hx, ex, hψ, hbase, evalPt_constFn G.hom y.left V h a,
      GlobalTheory.InvFieldBasis.evalPt_congr (Over.w y) ⊤ le_rfl le_rfl]
    have e2 : evalPt (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C).hom ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = algebraMap R C a :=
      evalPt_spMap (algebraMap R C) a
    rw [e2, TrivSqZeroExt.inr_zero, add_zero]
    exact (TrivSqZeroExt.algebraMap_eq_inl' R C C _).symm
  let w : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G := Over.homMk x hxp
  have ext : ∀ {B : Type} [CommRing B] [Algebra R B] (u u' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G),
      u.left = u'.left → u = u' := fun u u' e => Over.OverMorphism.ext e
  let fstR : DualNumber C →ₐ[R] C := TrivSqZeroExt.fstHom R C C
  let J : Ideal (DualNumber C) := RingHom.ker fstR
  have memJ : ∀ a : DualNumber C, a ∈ J ↔ a.fst = 0 := fun a => RingHom.mem_ker
  have hJ : J ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    rw [Ideal.mem_bot]
    have ea : a = inr a.snd := TrivSqZeroExt.ext ((memJ a).1 ha) rfl
    have eb : b = inr b.snd := TrivSqZeroExt.ext ((memJ b).1 hb) rfl
    rw [ea, eb, TrivSqZeroExt.inr_mul_inr]
  let g : C →ₐ[R] DualNumber C ⧸ J := (Ideal.Quotient.mkₐ R J).comp (TrivSqZeroExt.inlAlgHom R C C)
  have hg : Ideal.Quotient.mkₐ R J = g.comp fstR := by
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk J a = Ideal.Quotient.mk J (inl a.fst)
    refine Ideal.Quotient.eq.2 ((memJ _).2 ?_)
    simp
  have t1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ z = y := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp]
    have : fstR.comp (TrivSqZeroExt.inlAlgHom R C C) = AlgHom.id R C := AlgHom.ext fun _ => rfl
    rw [this, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id, Category.id_comp]
  have t2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ w = y := by
    refine ext _ _ ?_
    rw [Over.comp_left]
    have h' : ⊤ ≤ (spMap fstR.toRingHom ≫ x) ⁻¹ᵁ V := fun t _ => hx (Set.mem_univ _)
    refine ext_evalPt hV h' h (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ x V hx h' f).trans ?_
    rw [ex, hψ]
    exact add_zero _
  have hred : ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ z =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ w := by
    rw [hg, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, Category.assoc, t1, t2]
  obtain ⟨c, hc, hcu⟩ := GlobalTheory.SqZero.existsUnique_eq_lieExp_mul hv hJ hred
  have key : ∀ c' : Fin n → C, (w = GlobalTheory.SqZero.lieExp v (fun i => inr (c' i))
      (fun i => TrivSqZeroExt.inr_mul_inr _ _ _) * z) ↔
      ∀ f, δ f = ∑ a, c' a * evalPt y.left V h (dd a V f) := by
    intro c'
    obtain ⟨h₁, H₁⟩ := hdd (DualNumber C) (fun i => inr (c' i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) z V hz
    constructor
    · intro e f
      have := H₁ f
      rw [← GlobalTheory.InvFieldBasis.evalPt_congr (show x = _ from congrArg (fun u => u.left) e) V hx h₁,
        ex, hψ] at this
      simp only [ez] at this
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).1 this
    · intro e
      refine ext _ _ (ext_evalPt hV hx h₁ (RingHom.ext fun f => ?_))
      rw [H₁]
      change evalPt x V hx f = _
      rw [ex, hψ]
      simp only [ez]
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).2 (e f)
  have hinr : ∀ a : J, (a : DualNumber C) = inr (a : DualNumber C).snd := fun a =>
    TrivSqZeroExt.ext ((memJ _).1 a.2) rfl
  refine ⟨fun i => (c i : DualNumber C).snd, (key _).1 (hc.trans ?_), fun c' hc' => ?_⟩
  · rw [GlobalTheory.SqZero.lieExp_congr v (fun i => hinr (c i)) _ (fun i => TrivSqZeroExt.inr_mul_inr _ _ _)]
  · have hmem : ∀ i, inr (c' i) ∈ J := fun i => (memJ _).2 rfl
    have := hcu (fun i => ⟨inr (c' i), hmem i⟩) ((key c').2 hc')
    funext i
    exact congrArg (fun d : Fin n → J => (d i : DualNumber C).snd) this

theorem existsUnique_coeff_affine_ring : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  intro R _ G _ _ _ n v hv dd hdd V V' hV hV' hle δ hadd hmul hbase
  obtain ⟨t, ht, et⟩ := exists_evalPt_eq (R := Γ(G.left, V')) hV' (RingHom.id _)
  letI : Algebra R Γ(G.left, V') := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) Γ(G.left, V') ⟶ G :=
    Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
  have h : ⊤ ≤ y.left ⁻¹ᵁ V := fun s hs => hle (ht hs)
  have ev : ∀ s, evalPt y.left V h s = rsT s V' := fun s => by
    refine (evalPt_res t hle h ht s).symm.trans ?_
    rw [et, GlobalTheory.KS.rsT, dif_pos hle]
    rfl
  have := existsUnique_coeff_alg hv hdd y hV h δ hadd (by simpa only [ev] using hmul) hbase
  simpa only [ev] using this

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtDec

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem cv_act (Y : Ray oa) {T : Over (Sp R)} (t : T ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : T ⟶ Y.H) (χ : Q.X)
    (y : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L y J) :
    (GlobalTheory.TorusModel.cv (Y.Φ T ((t ≫ Y.i) * x)) χ y J : T.left.presheaf.stalk y) =
      gs (𝟙 T.left) y ⊤ (t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) *
        GlobalTheory.TorusModel.cv (Y.Φ T x) χ y J := by
  have h := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x (t ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := T) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one] at h
  rw [mul_comm (t ≫ Y.i) x, h, Units.val_mul, (Y.Φ_i t).2 χ y J hJ, _root_.mul_comm]
  exact congrArg (fun s => gs (𝟙 T.left) y ⊤ s * _) (GlobalTheory.SplitTorusPoints.coord_single t χ)

theorem preimage_stable (Y : Ray oa) (W : Q.P.A.left.Opens) :
    (snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) ≤
      ((fst (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H ≫ Y.i) * snd (splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) Y.H).left ⁻¹ᵁ
        (Y.q.left ⁻¹ᵁ W) := by
  have := Y.q_linear.isMonHom
  exact fun p hp => GlobalTheory.LevelExpansion.act_mem Y.isKernel _ _ p hp

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv in

theorem isAffineHom_q : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa), IsAffineHom Y.q.left := by
  intro R _ _ D O _ _ _ oa Y
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem isWt_of_uu : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    GlobalTheory.UU.IsWt Y.i V u χ → IsWt Y χ V u := by
  intro R _ _ Q O _ _ _ oa Y V u χ h S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have w : (x' * x⁻¹) ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by
    rw [← Hom.one_def, MonObj.mul_comp, hq, ← MonObj.mul_comp, mul_inv_cancel, MonObj.one_comp]
  let t := Y.isKernel.lift (x' * x⁻¹) (toUnit _) w
  have ht : t ≫ Y.i = x' * x⁻¹ := Y.isKernel.lift_fst _ _ _
  have hx' : (t ≫ Y.i) * x = x' := by rw [ht, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  have key : t.left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c χ) := fn_ext fun y _ => by
    choose J hJ using fun ψ : Sp S ⟶ Q.P.A.left => exists_chart Q.P.isLB (ψ y)
    have e1 := cv_act Y t x χ y J hJ
    rw [hx'] at e1
    have e2 := congrArg Units.val (hc χ y J hJ)
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial] at e2
    exact (Units.mul_left_inj _).1 (e1.symm.trans e2)
  have h₁ : ⊤ ≤ ((t ≫ Y.i) * x).left ⁻¹ᵁ V := by rw [hx']; exact hV'
  rw [WtAlg.valR_eq' _ _ hV', WtAlg.valR_eq' _ _ hV, ← GlobalTheory.TorusGrading.val_congr hx' h₁ hV' u, h _ t x h₁ hV, map_mul,
    key, Iso.inv_hom_id_apply]

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem uu_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (V : Y.H.left.Opens) (u : Γ(Y.H.left, V)) (χ : Q.X),
    IsWt Y χ V u → GlobalTheory.UU.IsWt Y.i V u χ := by
  intro R _ _ Q O _ _ _ oa Y V u χ h
  refine (GlobalTheory.CubCompare.isWt_iff_germ _ _ _ _).2 fun T z t x hx hx' => ?_
  obtain ⟨U, hU, hzU, hUle⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := x.left ⁻¹ᵁ V ⊓ ((t ≫ Y.i) * x).left ⁻¹ᵁ V) ⟨hx, hx'⟩
  let ρ : Sp Γ(T.left, U) ⟶ T.left := hU.fromSpec
  let φ : R →+* Γ(T.left, U) := (Spec.preimage (ρ ≫ T.hom)).hom
  have hφ : ρ ≫ T.hom = spMap φ := by simp [spMap, φ]
  let k : Over.mk (spMap φ) ⟶ T := Over.homMk ρ hφ
  have hr : ∀ p, ρ p ∈ U := fun p => by
    have : ρ p ∈ Set.range ρ := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨z', rfl⟩ : z ∈ Set.range ρ := by rw [hU.range_fromSpec]; exact hzU
  have hV₁ : ⊤ ≤ (k ≫ x).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).1
  have hV₂ : ⊤ ≤ (k ≫ ((t ≫ Y.i) * x)).left ⁻¹ᵁ V := fun p _ => (hUle (hr p)).2
  let c : Q.X → (Γ(T.left, U))ˣ := fun χ' => Units.map (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom.toMonoidHom
    (Units.map (k ≫ t).left.appTop.hom.toMonoidHom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ'))
  have hcv : ∀ χ', (unitOn (c χ')).val = (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val := fun χ' => by
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).hom.hom
      ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ').val)) = _
    exact Iso.hom_inv_id_apply _ _
  have e : k ≫ ((t ≫ Y.i) * x) = ((k ≫ t) ≫ Y.i) * (k ≫ x) := by rw [MonObj.comp_mul, Category.assoc]
  have hc : ∀ χ' y J, Good Q.P.L y J → val ((Y.Φ _ (k ≫ ((t ≫ Y.i) * x))).s χ') (𝟙 _) y J =
      gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ')) * val ((Y.Φ _ (k ≫ x)).s χ') (𝟙 _) y J := by
    intro χ' y J hJ
    rw [e]
    apply Units.ext
    rw [Units.val_mul, ← gs_unit _ y ⊤ trivial, hcv]
    exact cv_act Y (k ≫ t) (k ≫ x) χ' y J hJ
  have hq : (k ≫ ((t ≫ Y.i) * x)) ≫ Y.q = (k ≫ x) ≫ Y.q := by
    have := Y.q_linear.isMonHom
    exact Over.OverMorphism.ext (by simp only [Over.comp_left, Category.assoc, GlobalTheory.LevelExpansion.act_q Y.isKernel t x])
  have E := h Γ(T.left, U) φ (k ≫ x) (k ≫ ((t ≫ Y.i) * x)) c _ _ rfl rfl hV₁ hV₂ hq hc
  rw [WtAlg.valR_eq' _ _ hV₂, WtAlg.valR_eq' _ _ hV₁] at E
  have E' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom E
  rw [Iso.hom_inv_id_apply, map_mul, Iso.hom_inv_id_apply] at E'
  have E'' := congrArg (gs (𝟙 _) z' ⊤) E'
  rw [GlobalTheory.CubCompare.gs_appLE, gs_mul _ z' ⊤ trivial, GlobalTheory.CubCompare.gs_appLE] at E''
  have hcv' : (Scheme.ΓSpecIso (CommRingCat.of Γ(T.left, U))).inv.hom (c χ : Γ(T.left, U)) =
      (k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val := hcv χ
  have g1 : gs (𝟙 _) z' ⊤ ((k ≫ t).left.appTop.hom (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val) =
      gs (k ≫ t).left z' ⊤ (charUnit (Sp R) (GlobalTheory.RayEv.Chr Q) χ).val :=
    (gs_pull (𝟙 _) (k ≫ t).left z' ⊤ trivial _).trans (by rw [Category.id_comp])
  rw [hcv', g1] at E''
  apply (ConcreteCategory.bijective_of_isIso (ρ.stalkMap z')).1
  show (ρ.stalkMap z').hom _ = (ρ.stalkMap z').hom _
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv.charV
  rw [map_mul, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx' u, ← GlobalTheory.CubCompare.gs_comp ρ _ V z' hx u,
    ← gs_unit _ _ ⊤ trivial, ← GlobalTheory.CubCompare.gs_comp ρ _ ⊤ z' trivial]
  exact E''

end GlobalTheory.Heat.WtDec

namespace GlobalTheory.Heat.WtDec

theorem existsUnique_weights : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t) := by
  intro R _ _ Q O _ _ _ oa Y W hW f
  have hi : IsMonHom Y.i := Y.i_linear.isMonHom
  have := isAffineHom_q Y
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights (Sp R) Y.H (GlobalTheory.RayEv.Chr Q) Y.i hi _ (hW.preimage Y.q.left)
    (preimage_stable Y W)
  obtain ⟨a, ha, rfl⟩ := ex f
  refine ⟨a, ⟨fun χ => isWt_of_uu Y _ _ χ (ha χ), rfl⟩, fun F hF => ?_⟩
  let F' : GlobalTheory.RayEv.Chr Q →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) := F
  have e := un (F' - a) (fun χ => uu_of_isWt Y _ _ χ (WtAlg.isWt_sub (hF.1 χ) (isWt_of_uu Y _ _ χ (ha χ))))
    (by rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]; exact sub_eq_zero.2 hF.2.symm)
  exact sub_eq_zero.1 e

end GlobalTheory.Heat.WtDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOneStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  first | exact @GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one | exact GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one | (intros; apply GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitValueTranslatedBundleSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_value_translated_bundleSection : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))), (¬ ∀ j, s.f j = 0) → ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  first | exact @GlobalTheory.UnitPt.exists_unit_sval | exact GlobalTheory.UnitPt.exists_unit_sval | (intros; apply GlobalTheory.UnitPt.exists_unit_sval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldCoeffsGluedFromAffineOpens
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffGlue

theorem affine_cover {X : Scheme.{0}} (O : X.Opens) :
    O ≤ ⨆ l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O}, l.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (O : Set X) from hx) O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, fun y hy => hle hy⟩, hxU⟩

theorem exists_coeff : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro X n W δ dd hδ hdd H
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose c hc using fun j : J => (H j.1 j.1 j.2.1 j.2.1 j.2.2 le_rfl).exists
  have hl : ∀ (l : J) (O : X.Opens) (h : l.1 ≤ O), O ≤ W → ∀ f : Γ(X, O),
      rsT (δ O f) l.1 = ∑ a, c l a * rsT (dd a O f) l.1 := by
    intro l O h hO f
    have e1 := hδ.2.2 O l.1 h hO f
    have e2 := hc l (resG X h f)
    simp only [GlobalTheory.KS.rsT_self] at e2
    rw [GlobalTheory.KS.rsT_of_le h, ← e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.2 O l.1 h le_top f, GlobalTheory.KS.rsT_of_le h]
  have sub : ∀ j l : J, l.1 ≤ j.1 → ∀ a, rsT (c j a) l.1 = c l a := by
    intro j l h a
    refine congrFun ((H j.1 l.1 j.2.1 l.2.1 j.2.2 h).unique (y₁ := fun a => rsT (c j a) l.1) (y₂ := c l) ?_ ?_) a
    · intro f
      have := hc j f
      simp only [GlobalTheory.KS.rsT_self] at this
      rw [this, GlobalTheory.KS.rsT_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [GlobalTheory.KS.rsT_mul]
    · exact hl l j.1 h j.2.2
  have glue : ∀ a, ∃ s : Γ(X, W), ∀ j : J, rsT s j.1 = c j a := fun a => by
    refine GlobalTheory.KS.exists_rsT_eq (fun j : J => j.1) (fun j => j.2.2) (affine_cover W) (fun j => c j a)
      fun j k => ?_
    refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ j.1 ⊓ k.1} => l.1)
      (fun l => l.2.2) (affine_cover _) _ _ fun l => ?_
    have hj : l.1 ≤ j.1 := l.2.2.trans inf_le_left
    have hk : l.1 ≤ k.1 := l.2.2.trans inf_le_right
    rw [GlobalTheory.KS.rsT_rsT inf_le_left l.2.2, GlobalTheory.KS.rsT_rsT inf_le_right l.2.2,
      sub j ⟨l.1, l.2.1, hj.trans j.2.2⟩ hj, sub k ⟨l.1, l.2.1, hk.trans k.2.2⟩ hk]
  choose s hs using glue
  refine ⟨s, fun O hO f => ?_⟩
  refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O} => l.1) (fun l => l.2.2)
    (affine_cover O) _ _ fun l => ?_
  rw [hl ⟨l.1, l.2.1, l.2.2.trans hO⟩ O l.2.2 hO f, GlobalTheory.KS.rsT_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_rsT hO l.2.2, hs a ⟨l.1, l.2.1, l.2.2.trans hO⟩]

end GlobalTheory.VertCoeffGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_extending_affineDerivation : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U), (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) → ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  first | exact @GlobalTheory.DerFieldExt.exists_field | exact GlobalTheory.DerFieldExt.exists_field | (intros; apply GlobalTheory.DerFieldExt.exists_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldGluedOpenCoverStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_glued_openCover : ∀ (Z : Scheme.{0}) (J : Type) (V : J → Z.Opens) (e : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), (∀ i, IsField (V i) (e i)) → (∀ i j (O : Z.Opens), O ≤ V i → O ≤ V j → ∀ f, e i O f = e j O f) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (⨆ i, V i) d ∧ ∀ i (O : Z.Opens), O ≤ V i → ∀ f, d O f = e i O f := by
  first | exact @GlobalTheory.LogKS.isField_glue | exact GlobalTheory.LogKS.isField_glue | (intros; apply GlobalTheory.LogKS.isField_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InversionOfAdjunctionProjStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inversion_of_adjunction_proj_alt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  first | exact @GlobalTheory.inversion_of_adjunction_proj | exact GlobalTheory.inversion_of_adjunction_proj | (intros; apply GlobalTheory.inversion_of_adjunction_proj <;> assumption)
end

