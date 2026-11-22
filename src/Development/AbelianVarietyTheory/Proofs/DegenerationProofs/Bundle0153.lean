import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianLocusEqTrivialTorusLocusProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.AbelianPart

theorem isProper_snd_iff {Z A B T : Scheme.{0}} (e : A ≅ B) (f : A ⟶ Z) (g : B ⟶ Z) (h : e.hom ≫ g = f)
    (t : T ⟶ Z) : IsProper (pullback.snd f t) ↔ IsProper (pullback.snd g t) := by
  subst h
  have P : IsPullback (pullback.fst g t ≫ e.inv) (pullback.snd g t) (e.hom ≫ g) t :=
    IsPullback.of_iso (IsPullback.of_hasPullback g t) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  constructor
  · intro h
    rw [← P.isoPullback_hom_snd]
    infer_instance
  · intro h
    rw [← P.isoPullback_inv_snd]
    infer_instance

theorem abLocus_congr {Z : Scheme.{0}} (A B : Over Z) (e : A.left ≅ B.left) (h : e.hom ≫ B.hom = A.hom) :
    abLocus A = abLocus B := by
  ext z
  exact ⟨fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).1 (H K t ht),
    fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).2 (H K t ht)⟩

theorem isProper_snd_of_le {Z A : Scheme.{0}} (f : A ⟶ Z) {U V : Z.Opens} (h : U ≤ V)
    [IsProper (pullback.snd f V.ι)] : IsProper (pullback.snd f U.ι) := by
  have P := (IsPullback.of_hasPullback (pullback.snd f V.ι) (Z.homOfLE h)).paste_horiz
    (IsPullback.of_hasPullback f V.ι)
  rw [Scheme.homOfLE_ι] at P
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem not_mem_abLocus (C : GlobalTheory.ZJ.Core) (L : C.Law) {p : ℕ} [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z)
    (τ : C.Test y) (h : ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) :
    y (GlobalTheory.ZJ.cPt p) ∉ abLocus C.GG := by
  intro hm
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZJ.core_basic C
  have hc : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀ := (L.test p y τ).1
  have P := (IsPullback.of_hasPullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).paste_horiz hc
  rw [Category.assoc, τ.fac] at P
  refine h ((GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff C.GG P (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p))).1 ?_)
  have e : GlobalTheory.ZJ.rPt p (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p)) = GlobalTheory.ZJ.cPt p :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue (GlobalTheory.ZJ.OO p))
  rw [← e] at hm
  exact hm

theorem ab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab := by
  rintro o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, -⟩ ⟨L⟩ hT hC hO h₁ h₂
  obtain ⟨hab, hpr⟩ := GlobalTheory.ZJ.AbelianLocus.abLocus_eq ex.core L hT hC ⟨_, hO⟩ h₁ (fun z hz hn => by
    obtain ⟨p, _, y, τ, rfl, h⟩ := h₂ z hz hn
    exact not_mem_abLocus ex.core L y τ h)
  have hE : abLocus Z.G = {z | S.TT M z = ⊥} := (abLocus_congr Z.G ex.core.GG e he).trans hab
  refine ⟨hE, fun W hW => ?_⟩
  rw [hE] at hW
  exact (isProper_snd_iff e _ _ he W.ι).2
    (@isProper_snd_of_le _ _ ex.core.GG.hom W ⟨_, hO⟩ hW hpr)

end GlobalTheory.ZH.AbelianPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesCubeValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartIso_carries_cube_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x y u, (N'.θ (f x) (f y) (f u) : F) * wVal ν ν' w f (x * y) * wVal ν ν' w f (x * u) * wVal ν ν' w f (y * u) * wVal ν ν' w f 1 = (N.θ x y u : F) * wVal ν ν' w f (x * y * u) * wVal ν ν' w f x * wVal ν ν' w f y * wVal ν ν' w f u := by
  first | exact @GlobalTheory.Ex.AbPartCube.theta_move | exact GlobalTheory.Ex.AbPartCube.theta_move | (intros; apply GlobalTheory.Ex.AbPartCube.theta_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesSymmetryValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartIso_carries_symmetry_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  first | exact @GlobalTheory.AbPartSym.sym_values | exact GlobalTheory.AbPartSym.sym_values | (intros; apply GlobalTheory.AbPartSym.sym_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_psi_valuation_eq_half_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  first | exact @GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | exact GlobalTheory.ArcPsiVal.q_eq_of_hasArcData | (intros; apply GlobalTheory.ArcPsiVal.q_eq_of_hasArcData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumPullbackRescaledMatchesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatum_pullback_rescaled_matches : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] (f : O' →+* R) (D' : DegPre R) (hD : IsPullDeg f a.D₀ D') (u₀ : R) (uK : (FractionRing R)ˣ), (uK : FractionRing R) = algebraMap R _ u₀ → ∀ (q : D'.X → (FractionRing R)ˣ) (Φ : D'.P.A.left ⟶ a.D₀.P.A.left), Φ = PsiEvenPull.proj hD → (∀ y, q y = uK ^ (a.be (hD.xe y) (hD.xe y) / 2)) → ∃ (_ : Module (𝓞 E) (TauTwist.rescale D' q).X) (oW : letI := H.starRing; (TauTwist.rescale D' q).OAct (𝓞 E)) (he : _) (w : _) (e : _), GlobalTheory.LN.Match a f u₀ (TauTwist.rescale D' q) oW Φ he w e ∧ (∀ y, hD.xe (e y) = y) ∧ (TauTwist.rescale D' q).PsiEven ∧ (TauTwist.rescale D' q).TauBimult := by
  first | exact @GlobalTheory.RescaleMatch.exists_match_rescale | exact GlobalTheory.RescaleMatch.exists_match_rescale | (intros; apply GlobalTheory.RescaleMatch.exists_match_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionLabelsActionCompat
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel
open GlobalTheory.TorusExt

theorem b_eq_of_equiv {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {j : ℕ} (hj : 0 < j) {p p' : QkPt D F j}
    (h : QkPt.Equiv D F p p') (hy : p.y = 0) (hy' : p'.y = 0) : p'.g.b = p.g.b := by
  letI := gtGroup D F
  obtain ⟨z, h₁, h₂⟩ := (equiv_iff hB _ _).1 h
  rw [hy, hy', zero_add] at h₁
  have hz : z = 0 := by
    have : (j : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h₁.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hj.ne')
  rw [h₂, hz, map_zero, add_zero]

theorem act_compat_on_torsion : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  intro hL hBr E _ _ _ H D R _ _ C _ _ _ A o M hT N' ν' k β u r J j hj hr hlab x b hb
  letI := H.starRing
  have hG := hL.globalFns
  have hB := A.bimult
  have hB' : M.P.D.toPre.TauBimult := M.P.D.tau_bimult
  obtain ⟨-, -, -, -, br⟩ := hBr R A.D₀ A.even A.bimult C A.N A.ν
  obtain ⟨-, -, -, -, br'⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even hB' C N' ν'
  obtain ⟨e1, -, e3⟩ := br j
  obtain ⟨-, e2', e3'⟩ := br' j
  obtain ⟨τ, hτ, hQ, -⟩ := (twJ_mulEquiv C A.N N' k β u J).1 r j hr
  obtain ⟨f, f1, -, f3, -, f5, -⟩ := hT C j hj

  have key : ∀ (v : D.La) (p : QkPt A.D₀ C j), QkPt.Equiv A.D₀ C (A.I.ev j v) p → p.y = 0 →
      ∃ p' : QkPt M.P.D.toPre C j, p'.y = 0 ∧ p'.g.b = ν'.eA (J.φ (A.ν.eA.symm p.g.b)) ∧
        (f p').left = (o.I.ev j v).left ≫ M.φ := by
    intro v p hp hy
    obtain ⟨q, hq, -⟩ := e1 p
    obtain ⟨p', hp'⟩ := e2' (τ q)
    obtain ⟨pv, hpv⟩ := e2' (τ (A.q j v))
    have hE : QkPt.Equiv _ C pv p' := (e3' _ _ _ _ hpv hp').2 ((hQ _ _).1 ((e3 _ _ _ _ (A.hq j v) hq).1 hp))
    obtain ⟨t, t1, t2, t3⟩ := (hτ q _).1 rfl
    obtain ⟨s, s1, s2, s3⟩ := (hτ (A.q j v) _).1 rfl
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev j v).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (f1 _ _).1 (hlab v s _ pv z s1 s2 s3 hpv rfl)
    refine ⟨p', ?_, ?_, ?_⟩
    · have h0 : q.1.1.toAdd = 0 := A.ν.eX.injective (hq.1.trans (hy.trans (map_zero _).symm))
      rw [← hp'.1, t2, t1.1]
      erw [h0, map_zero, map_zero]
    · rw [← hp'.2.1, t3.1, t1.2.1, ← hq.2.1, MulEquiv.symm_apply_apply]
    · rw [← (f3 _ _).2 hE, ← hz]
      rfl
  obtain ⟨p₀, y₀, b₀⟩ := exists_qkPt_of_torsion (F := C) hB hj.ne' (b := A.ν.eA b) (by rw [← map_pow, hb, map_one])
  obtain ⟨v, hv⟩ := A.I.onto j hj p₀
  have hv₁ : QkPt.Equiv A.D₀ C (A.I.ev j (x • v)) (qkSmul hB hG A.oa x p₀) :=
    (qkAct_iff_of_equiv hB hG A.oa hv (A.I.lin j hj x v)).1 (qkAct_qkSmul hB hG A.oa x p₀)
  obtain ⟨p₀', c₀, d₀, g₀⟩ := key v p₀ hv y₀
  obtain ⟨p₁', c₁, d₁, g₁⟩ := key (x • v) _ hv₁ (by
    change x • p₀.y = 0
    rw [y₀, smul_zero])
  have hf : f (qkSmul hB' hG M.P.oD x p₀') = f p₁' := by
    rw [f5 x _ _ (qkAct_qkSmul hB' hG M.P.oD x p₀')]
    refine Over.OverMorphism.ext ?_
    rw [g₁, Over.comp_left, g₀, o.I.lin, Over.comp_left, Category.assoc, Category.assoc, M.act]
  have hb' := b_eq_of_equiv hB' hj ((f3 _ _).1 hf) (by
    change x • p₀'.y = 0
    rw [c₀, smul_zero]) c₁
  have a₁ : (qkSmul hB' hG M.P.oD x p₀').g.b = p₀'.g.b ≫ M.P.oD.onB.act x := gtSmul_b hG M.P.oD x _
  have a₀ : (qkSmul hB hG A.oa x p₀).g.b = p₀.g.b ≫ A.oa.onB.act x := gtSmul_b hG A.oa x _
  rw [d₁, a₁, a₀, d₀, b₀, MulEquiv.symm_apply_apply] at hb'
  unfold actV
  rw [← hb', MulEquiv.symm_apply_apply]

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharEqZeroOfIsProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AbelianLocus

theorem char_eq_zero_of_isProper {k : Type} [Field k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G]
    (D : E.GtDatum G) [IsProper G.hom] (a : E.X) : a = 0 := by
  have hi := D.i_hom
  have h1 := GlobalTheory.splitTorus_hom_proper_trivial_field k E.X G D.i hi
  have h2 : 𝟙 (splitTorus (Sp k) E.X) = toUnit _ ≫ η[splitTorus (Sp k) E.X] := by
    refine D.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.id_comp, Category.assoc, IsMonHom.one_hom]
    exact h1
  have h3 := Rosenlicht.torusGamma_chi k E.X a
  rw [Rosenlicht.chi, h2, Rosenlicht.coord_toUnit_comp, Rosenlicht.torusGamma_const] at h3
  by_contra ha
  have h4 := congrArg (fun f : AddMonoidAlgebra k E.X => f.coeff a) h3
  simp [Ne.symm ha] at h4

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem perp_top_eq_bot (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem proj_eq_one {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : IsClosed ({z} : Set M.Z))
    (hT : S.TT M z = ⊥) : ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => hB.zero z hc _
    (by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨a, rfl⟩)
    (by rw [proj_eq_one hT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec])
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hw : IsClosed ({w} : Set Q.P.left)) (hT : S.TT M (Q.P.hom w) = ⊥) : w ∈ Q.G := by
  have := Q.proper
  have hc : IsClosed ({Q.P.hom w} : Set M.Z) := by
    rw [← Set.image_singleton]
    exact Q.P.hom.isClosedMap _ hw
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc hT
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inl hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_eq_one hT, Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem abelian_locus : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → IsOpen {z : M.Z | S.TT M z = ⊥} ∧ (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hbig hgeo _
  refine ⟨isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, fun z' h => ?_, OpenPart.isOpen_supI_subset (S := S) z,
    fun _ h => h⟩, mem_G hB Q, fun z hz hT => ?_⟩
  · exact le_bot_iff.1 ((OpenPart.TT_le_TT h).trans (le_of_eq hz))
  obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hbig hgeo
  obtain ⟨p, hp, y, hy⟩ := h2 z hz
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := h1 p y hy.2
  obtain ⟨τ, e, he, -⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hbig
  refine ⟨p, hp, y, τ, hy.1, fun hpr => hT ?_⟩
  have : IsProper t.mod.Φ.G.hom := by
    rw [← he] at hpr
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).1 hpr
  have h0 := char_eq_zero_of_isProper t.mod.Φ.E t.mod.Φ.G t.mod.Φ.D
  obtain ⟨e', -⟩ := t.mt
  have hk : t.τ.yy.ker = ⊤ := by
    refine top_unique fun a _ => ?_
    obtain ⟨α, hα⟩ := QuotientAddGroup.mk_surjective (t.τ.yy a)
    have : α = 0 := (e'.trans t.mod.xe.symm).map_eq_zero_iff.1 (h0 _)
    rw [AddMonoidHom.mem_ker, ← hα, this]
    rfl
  rw [ThetaSys.TT, hB.atTest z p y y₀ t.τ hy c.at_, hk, perp_top_eq_bot]

end GlobalTheory.ZH.AbelianLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationIsoCommInducedLabelMapsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationIso_comm_induced_label_maps : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  first | exact @GlobalTheory.ModelData.iso_comm_of_labels | exact GlobalTheory.ModelData.iso_comm_of_labels | (intros; apply GlobalTheory.ModelData.iso_comm_of_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionThetaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  first | exact @GlobalTheory.Ex.FibIso.exists_iso_fib | exact GlobalTheory.Ex.FibIso.exists_iso_fib | (intros; apply GlobalTheory.Ex.FibIso.exists_iso_fib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianPartIsoThetaSectionScaleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianPartIso_theta_section_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  first | exact @GlobalTheory.Ex.AbPartIso.exists_th_scale | exact GlobalTheory.Ex.AbPartIso.exists_th_scale | (intros; apply GlobalTheory.Ex.AbPartIso.exists_th_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGauge
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ArcLift

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem local_noeth {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) :
    IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

theorem exists_lift : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  intro hL hG E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb F _ _ _ S hS
  obtain ⟨_, _⟩ := local_noeth hb
  obtain ⟨N, ν, hν⟩ := GlobalTheory.T.exists_integral_degeneration_values hL O' a.D₀ a.even a.bimult F S hS
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hrW : H.rt0 ∈ W₀ := mem_of_pow_mem W₀ two_ne_zero (by
    rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W₀ _))
  have hzW : zeta l.A ∈ W₀ := mem_of_pow_mem W₀ l.A_pos.ne' (by
    rw [zeta, (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]; exact one_mem _)
  let r : c.V W₀ := ⟨⟨H.rt0, hr⟩, hrW⟩
  let z : c.V W₀ := ⟨⟨zeta l.A, hz⟩, hzW⟩
  obtain ⟨hdet, I, hζ, hA, hM⟩ := a.geom F r z rfl rfl _ rfl
  have hq := fun n (v : D.La) =>
    (((hG O' a.D₀ a.even a.bimult F N ν).2.2.2.2 n).1 (I.ev n v)).exists
  choose q hq using hq
  have hr2 : r ^ 2 = -(H.d : c.V W₀) := by
    apply Subtype.ext; apply Subtype.ext
    simpa [r] using H.sqrt_neg_disc_sq
  refine ⟨{ ρ := algebraMap (FractionRing O') F (algebraMap O' _ (b r))
            ρ_sq := by rw [← map_pow, ← map_pow, ← map_pow, hr2, map_neg, map_neg, map_neg, map_natCast, map_natCast, map_natCast]
            det := fun τ => by
              obtain ⟨n, h1, h2⟩ := hdet τ
              exact ⟨n, h1, by
                rw [h2]
                by_cases h : τ H.rt = algebraMap (FractionRing O') F (algebraMap O' _ (b r))
                · rw [if_pos h]; exact if_pos h
                · rw [if_neg h]; exact if_neg h⟩
            I := I, N := N, ν := ν, q := q, hq := hq
            be := { be := a.be.comp ν.eX.toIntLinearEquiv.toLinearMap ν.eX.toIntLinearEquiv.toLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ (by simpa using hy)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r' h => by
              obtain rfl : r' = r := Subtype.ext (Subtype.ext h)
              rfl
            ζ_eq := fun z' h => by
              obtain rfl : z' = z := Subtype.ext (Subtype.ext h)
              exact hζ
            levA := hA
            levM := hM
            closed := inferInstance }, hν⟩

end GlobalTheory.Ex.ArcLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTraitStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_recombination_invertible_matrix_trait : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  first | exact @GlobalTheory.Recombine.exists_recombination | exact GlobalTheory.Recombine.exists_recombination | (intros; apply GlobalTheory.Recombine.exists_recombination <;> assumption)
end

