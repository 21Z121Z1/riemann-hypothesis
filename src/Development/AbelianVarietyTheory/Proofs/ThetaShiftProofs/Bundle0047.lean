import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.ArcCM.cfOf_linear_and_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ d a' n
  have hP : ∀ F ∈ sec Xo c a' n, ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁),
      algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (absA Dw a') := fun F hF =>
    GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF
  have hcomp : ∀ a : c.F, algebraMap c.F (ArcS Dw K₁) a =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)
        (algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a) := fun _ => rfl
  have hnum : ∀ F : sec Xo c a' n,
      algebraMap _ (ArcS Dw K₁) (arcNum (evR Xo c F.1 d.yF)) = evR Xo c F.1 d.yF := fun F =>
    (hP F.1 F.2).elim fun P hP' => by
      rw [← hP'.1, LinOfPoly.arcNum_map]
  have hadd : ∀ F G : sec Xo c a' n, arcNum (evR Xo c (F + G).1 d.yF) =
      arcNum (evR Xo c F.1 d.yF) + arcNum (evR Xo c G.1 d.yF) := fun F G =>
    LinOfPoly.inj _ K₁ (by
      rw [map_add, hnum, hnum, hnum, Submodule.coe_add, LinOfPoly.evR_add])
  have hsmul : ∀ (a : c.F) (F : sec Xo c a' n), arcNum (evR Xo c (a • F).1 d.yF) =
      algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a *
        arcNum (evR Xo c F.1 d.yF) := fun a F =>
    LinOfPoly.inj _ K₁ (by
      rw [hnum, Submodule.coe_smul, LinOfPoly.evR_smul, map_mul, hnum F, hcomp])
  refine ⟨⟨{ toFun := fun F => cfOf d.yF d.μ d.jj F.1, map_add' := ?_, map_smul' := ?_ }, fun F => rfl⟩, ?_⟩
  · intro F G
    simp only [cfOf]
    rw [hadd, MvPolynomial.coeff_add, HahnSeries.coeff_add]
  · intro a F
    simp only [cfOf]
    rw [hsmul, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul, LinOfPoly.laur_alg,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, RingHom.id_apply]
    simp [Algebra.smul_def]
  · intro F hF hne
    obtain ⟨P, hP1, hP2⟩ := hP F hF
    rw [← Finsupp.degree_eq_sum]
    by_contra hd
    apply hne
    simp only [cfOf]
    rw [← hP1, LinOfPoly.arcNum_map, hP2.coeff_eq_zero hd]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.DiscInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem flat_of_injective {A V : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing V] [IsDomain V]
    (f : A →+* V) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).2 hf
  show Module.Flat A V
  infer_instance

theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {G : SAB H S'} {t' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap G t f) (n : SABMap t' G g) (k : SABMap t' t h) (hb : h = g ≫ f)
    (hφ : k.φ = n.φ ≫ m.φ) (θ : LB.Sec t.PP.L) (w : LB.Iso t'.PP.L (t.PP.L.pull k.φ)) (σ : LB.Sec t'.PP.L)
    (θ2 : LB.Sec (t.PP.L.pull k.φ)) (r : RigIso k w) (hi : IsoMaps w σ θ2) (hp : PullSec k.φ θ θ2) :
    ∃ (θ' : LB.Sec G.PP.L) (w' : LB.Iso t'.PP.L (G.PP.L.pull n.φ)),
      (∀ s : S', (∃ x : t.G.left, t.G.hom x = f s ∧ x ∈ Out.nonzeroLocus θ) →
        ∃ x : G.G.left, G.G.hom x = s ∧ x ∈ Out.nonzeroLocus θ') ∧
      RigIso n w' ∧ IsoMaps w' σ (thfPull G.PP.L n.φ θ') := by
  obtain ⟨w0, g0, r0, -⟩ := m.lin
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ
  have he : k.cm.e = n.cm.e ≫ m.cm.e := by rw [k.base, n.base, m.base, hb]
  obtain ⟨w', r', tri⟩ := GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r
  refine ⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩
  · rintro s ⟨z, hz, hz'⟩
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z s hz
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have u₁ : IsUnit (gs m.φ y _ (θ.f j)) := by rw [gs_stalkMap m.φ y _ hj]; exact u.map _
    have e := hθ' _ (𝟙 _) y j i hj hi
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · have hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (n.φ y))
    have pt : k.φ y = m.φ (n.φ y) := congrArg (fun q => q y) hφ
    have hj' : k.φ y ∈ t.PP.L.U j := pt ▸ hj
    have e1 := hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'
    have e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k') := by
      have hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k' := ⟨mem_pull.2 hj', hy.2⟩
      have le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      have a := congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')
      refine (gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_
      rw [← hp (fun _ => j) le]
      exact (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2
    have e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ := by rw [Category.assoc, hφ]
    rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
    refine (gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.ArcQ.DiscInt

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

open DiscInt in

theorem integral_of_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ ρ e th hB hth hPI T io ev hinj hρ
  letI := io.toAlgebra
  intro y hy
  obtain ⟨z, t', m1, k, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, p2, hg⟩ := hy
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G W.t (spMap ev)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ev) W.t
    exact ⟨_, ⟨m⟩⟩
  have hb := sp_comp ev (algebraMap T.V T.Fr)
  obtain ⟨n, hn⟩ : ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
    have key : ∀ (g : Sp T.Fr ⟶ _) (k : SABMap t' W.t g), g = spMap (algebraMap T.V T.Fr) ≫ spMap ev →
        ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
      intro g k hg
      subst hg
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m k
    exact key _ k hb
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB T.V ev
    (flat_of_injective _ hinj) G m
  have eig : ∀ (τ : E →+* ℂ) (w : epsR T.V ⟶ G.G), IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left =
      spMap (epsScaleR (ev (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left := fun τ w =>
    ⟨fun h x => h x _ (hρ τ x).symm, fun h x s hs => by
      obtain rfl : s = ev (PowerSeries.C (R := A) (ρ τ x)) := IsFractionRing.injective T.V T.Fr (hs.trans (hρ τ x))
      exact h x⟩
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m n k hb hn θ w2 σ θ2 r2 i2 p2
  refine ⟨G, t', m1, n, ⟨u, fun τ i => (isTan_iff _).2 ((hu2 τ).1 i).1, fun τ i => (eig τ _).2 ((hu2 τ).1 i).2,
    fun τ w h1 h2 => (hu2 τ).2 w ((isTan_iff _).1 h1) ((eig τ w).1 h2), fun τ i => ?_⟩, θ',
    GlobalTheory.T.polarisation_section_generates_of_special_fibre hL hL2 E H Dw l Xo c T G t' y.x m1 n θ'
      (hnz _ (GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ (Or.inr hPI) _).2),
    w1, w', σ, s1, thfPull G.PP.L n.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨v, p, h1, h2, h3, pb⟩ := hu τ i
  obtain ⟨v', h1', h3'⟩ := hu1 τ i
  obtain rfl : v = v' := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ i)).1.unique h1 h1'
  refine ⟨p, h2, ?_⟩
  apply m.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact (congrArg _ hn.symm).trans (h3.trans (by rw [dual_comp, Category.assoc]; exact congrArg _ h3'.symm))
  · have ub : (u τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (u τ i)
    rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, pb]
    exact ((congrArg _ ub).trans (dual_alg _)).symm

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaTheta
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem eq_at_zero_of_eq_off_zeros {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F p q : V → ℂ}
    (hF : Continuous F) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) {v₀ : V} (h₀ : F v₀ ≠ 0)
    (h : ∀ v, F v ≠ 0 → p v = q v) : p 0 = q 0 := by
  have hl : Differentiable ℂ fun t : ℂ => t • v₀ := differentiable_id.smul_const _
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => p (t • v₀)) Set.univ := fun t _ => (hp.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => q (t • v₀)) Set.univ := fun t _ => (hq.comp hl).analyticAt t
  have h3 : ∀ᶠ t in nhds (1 : ℂ), F (t • v₀) ≠ 0 :=
    (hF.comp hl.continuous).continuousAt.eventually_ne (by simpa using h₀)
  have h4 := AnalyticOnNhd.eq_of_eventuallyEq h1 h2 (h3.mono fun t ht => h _ ht)
  simpa using congrFun h4 0

theorem isFnInRigFrame_of_isFn {D₀ : Out.DegPre ℂ} {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) (hr : u.IsRig D₀.rig)
    {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ} (hθ : u.IsFn th θ) {p : (Fin g → ℂ) → (Fin n → ℂ)}
    (hp : Differentiable ℂ p) (hp0 : p 0 = 0) {Q ϑ : (Fin g → ℂ) → ℂ} (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 0)
    (h : ∀ z, θ (p z) = Complex.exp (Q z) * ϑ z) :
    IsFnInRigFrame D₀ (fun z => (u.ex (p z)).left) th ϑ := by
  refine ⟨fun j z => Complex.exp (Q z) * u.fr j (p z), fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hj => ?_, fun j z hz => ?_⟩
  · exact hQ.cexp.differentiableOn.mul ((u.fr_hol j).comp hp.differentiableOn fun z hz => hz)
  · exact mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne j _ hz)
  · beta_reduce
    rw [u.fr_compat j j' _ hz]
    ring
  · have e1 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
    have e2 : (u.ex 0).left = eSec D₀.P.A := by
      rw [e1, Hom.one_def, toUnit_unit, Category.id_comp]
      rfl
    beta_reduce at hj ⊢
    rw [hp0, e2] at hj
    rw [hQ0, hp0, Complex.exp_zero, _root_.one_mul]
    exact hr (fun _ => j) fun x hx => Set.mem_iInter.2 fun _ => hj hx
  · beta_reduce
    rw [hθ j _ hz, h]
    ring

set_option maxHeartbeats 800000 in

theorem arc_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  obtain ⟨T₀, hT⟩ := Λ.A.exists_isConvLine
  refine ⟨max T₀ (max T₁ K.T), fun T hTT th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ hth hEF hS hP hc₁ hc₂ r₂ r₁ r₀ hex => ?_⟩
  have hT0 : T₀ ≤ T := (le_max_left _ _).trans hTT
  have hT1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTT
  have hTK : K.T ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hTT
  obtain ⟨θ, hθ, hθ0, hfn⟩ := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.2 th hth.1
  let bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ.A.La := bas.trans (K.gam.toAddEquiv.toIntLinearEquiv)
  have hb : ∀ u, bas' u = K.gam (bas u) := fun _ => rfl
  obtain ⟨hu, hτ, d₁, d₂, -, -, hdS, ⟨Q, κ, -, hQ, hQ0, hκ, hSum, hoff⟩, huniq⟩ :=
    Λ.A.theta_comparison hT K.h.toLinearEquiv hθ hθ0 bas' (fun u v => by rw [hb, hb, K.EF_eq, hEF]) S
      (fun u => by rw [← hS, hb, map_eq_zero_iff _ Λ.ε.injective]) h τ
      (fun w k => by simpa only [hb, K.Pw_eq, ContinuousLinearEquiv.coe_toLinearEquiv] using hP w k)
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv] at hSum hoff huniq
  have hSne : ∀ w : ℂ, T₀ < w.im → ∃ v, Λ.A.Sum 1 0 θ w v ≠ 0 := fun w hw => by
    obtain ⟨v, hv⟩ := Λ.A.exists_Sum_ne_zero one_ne_zero 0 hθ0 fun z =>
      AnArc.summable_term hT one_ne_zero hθ hw (0, z)
    exact ⟨_, hv⟩
  have key : ∀ w : ℂ, T < w.im → ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w))
      (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr →
      ∃ (lam : ℂ) (f : Λ.A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧
        (∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (K.h v) = f v * Ψ.fr w j v) ∧
        ∀ v, Λ.A.Sum 1 0 θ w v = lam * thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) * f v := by
    intro w hw fr hfr
    have hw0 := hT0.trans_lt hw
    have tr : ∀ (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) ϑ, y = y' →
        IsThetaFrameAt Xo.univ.t.PP y e ϑ fr → IsThetaFrameAt Xo.univ.t.PP y' e ϑ fr := by
      rintro y _ e ϑ rfl h
      exact h
    refine GlobalTheory.T.two_rigidified_theta_frames_on_fibre hL hL2 E H D l Xo Λ.A lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) g K.h _ _ fr
      (hfib w (hT1.trans_lt hw)) (K.ex_eq w (hTK.trans_lt hw)) (tr _ _ _ _ (K.u_eq w (hTK.trans_lt hw)) hfr) ?_ θ hθ
      (hSne w hw0)
    obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level (hτ w hw0).1 (hτ w hw0).2 hc₁ hc₂).1
    obtain ⟨z', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu z
    exact ⟨z', hz⟩
  obtain ⟨rfl, rfl⟩ : c₁ = d₁ ∧ c₂ = d₂ := by
    obtain ⟨w, fr, hw, hfr⟩ := hex
    obtain ⟨lam, f, hlam, hf, hf0, -, -, hfS⟩ := key w hw fr hfr
    exact huniq c₁ c₂ hc₁ hc₂ w (hT0.trans_lt hw) (fun v => lam * f v) (hf.const_mul _)
      (fun v => mul_ne_zero hlam (hf0 v)) fun v => by rw [hfS]; ring
  refine ⟨κ, hκ, hdS, fun w _ => ?_, fun U s r hU _ hpull => ?_⟩
  · have e : (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) =
        fun z => (Λ.u.ex (K.h.symm z).2).left := funext fun z => Λ.ex0_b _
    rw [e]
    refine isFnInRigFrame_of_isFn Λ.u Λ.rig hfn (p := fun z => (K.h.symm z).2) K.h.symm.differentiable.snd
      (by simp) (Q := fun z => Q (K.h.symm z)) (hQ.comp K.h.symm.differentiable) (by simp [hQ0]) fun z => ?_
    rw [hoff w, ContinuousLinearEquiv.apply_symm_apply]
    ring
  · obtain ⟨T', hT'⟩ := GlobalTheory.T.arcSection_value_at_specialised_points_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r hfin hth hθ
      hθ0 hfn r₂ r₁ r₀ hU hpull
    refine ⟨max T T', fun w hw => ?_⟩
    have hw1 : T < w.im := (le_max_left _ _).trans_lt hw
    have hw0 := hT0.trans_lt hw1
    obtain ⟨rw, hrw, hval⟩ := hT' w ((le_max_right _ _).trans_lt hw)
    refine ⟨rw, hrw, fun fr hfr z x j k j₀ hx hx' hj hj₀ => ?_⟩
    obtain ⟨v, rfl⟩ := K.h.surjective z
    obtain ⟨lam, f, hlam, hf, hf0, hf1, hfr', hfS⟩ := key w hw1 fr hfr
    obtain ⟨v₀, hv₀⟩ := hSne w hw0
    have hlk : lam = κ := by
      have := eq_at_zero_of_eq_off_zeros (AnArc.differentiable_Sum hT one_ne_zero hθ hw0).continuous
        (hf.const_mul lam) (hQ.cexp.const_mul κ) hv₀ fun v hv => by
          have h1 := hfS v
          have h2 : thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) ≠ 0 := fun h0 => hv (by rw [h1, h0]; simp)
          refine mul_right_cancel₀ h2 ?_
          rw [← hSum w hw0 v, h1]
          ring
      simpa [hf1, hQ0] using this
    have hx2 : x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left := hx.trans (K.ex_eq w (hTK.trans_lt hw1) v)
    have hch : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
      rw [← hx2]
      exact fun p hp => Set.mem_iInter.1 (hj₀ hp).1 PUnit.unit
    rw [hval v x j k j₀ hx2 hx' hj hj₀, hfr' v j₀ hch, hfS, hlk]
    ring

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by
  rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)
    rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (MvPolynomial.coeff μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRationalStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  first | exact @GlobalTheory.ArcCM.mggOnto_of_detect | exact GlobalTheory.ArcCM.mggOnto_of_detect | (intros; apply GlobalTheory.ArcCM.mggOnto_of_detect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem modelsAt_of_good_level : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ModelsAt Xo c := by
  intro hK E _ _ _ H Dw l Xo c hr hg
  classical
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l', ModelsAt (Xs l) c := by
    intro Xs p W hp hW
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY p W hp hW
    exact ⟨Y p W hp hW ⟨l, c, hg p hp⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg p hp⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rwa [Function.update_self] at h

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.TransvPrinc

theorem transvIn_of_princ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {M N : ℕ}
    (hMN : M ∣ N) (la : Wt X.Ψ r)
    (hP : ∀ gm : GL (Fin r) E, IsUStab X.Gm X.Λ gm →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (gm : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → gm ∈ X.Γ)
    (hχ : ∀ gm ∈ X.Γ, X.χ la gm = 1) : TransvIn X N la := by
  intro ξ hξ s hs hc
  have hκ : cc (s * X.κ0) = -(s * X.κ0) := by
    have h0 := X.ξ0_im
    simp only [cc] at hs h0 ⊢
    rcases X.κ0_xi with h | h <;> simp [h, hs, h0, map_ofNat]
  have hn : ∀ (n : ℕ) u, u ∈ X.Λ → (n : E) • u ∈ X.Λ := fun n u hu => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hu n
  have hmem : GlobalTheory.FlagData.transv X.Gm hξ.2.1 (s * X.κ0) ∈ X.Γ := by
    refine hP _ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ (fun x hx => ?_)
    · exact GlobalTheory.FlagData.herm_transvMat X.Gm_herm hξ.2.1 hκ x y
    · obtain ⟨u, hu, e⟩ := hc x hx
      rw [sub_eq_iff_eq_add] at e
      change (transvMat _ _ _).mulVec x ∈ _
      rw [e]; exact add_mem (hn _ u hu) hx
    · change (transvMat _ _ _).mulVec x ∈ _ at hx
      obtain ⟨u, hu, e⟩ := hc _ hx
      have : x = (transvMat X.Gm ξ (s * X.κ0)).mulVec x - (N : E) • u := by
        rw [← e, GlobalTheory.FlagData.transvMat_mulVec _ _ (Matrix.mulVec _ _), GlobalTheory.FlagData.transvMat_mulVec,
          GlobalTheory.FlagData.herm_add_smul_left, hξ.2.1]
        simp
      rw [this]; exact sub_mem hx (hn _ u hu)
    · obtain ⟨m, hm⟩ := hMN
      obtain ⟨u, hu, e⟩ := hc x hx
      refine ⟨(m : E) • u, hn m u hu, ?_⟩
      change (transvMat _ _ _).mulVec x - x = _
      rw [e, hm, smul_smul]
      push_cast; rfl
  exact ⟨_, hmem, rfl, hχ _ hmem⟩

theorem transvIn_of_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.FrameNorm.HasPrinc U l.M → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → ∀ k, TransvIn (U.X k) l.M' (laU U a' n k) := by
  intro E _ _ _ H Dw l Xo c σ r U a' n hP hχ k
  exact transvIn_of_princ (U.X k) (Nat.dvd_lcm_left _ _) _ (hP k) (hχ k)

end GlobalTheory.TransvPrinc
end

