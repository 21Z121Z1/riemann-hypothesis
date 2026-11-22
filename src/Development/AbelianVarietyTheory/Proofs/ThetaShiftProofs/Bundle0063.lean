import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianPartSectionNormSqEqThetaData
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0060
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianPartSectionNormSqEqThetaDataStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (v : ℝ), Ha.T < w.im → Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → v = ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ := by
  first | exact @GlobalTheory.AbelianPartNorm.norm_eq | exact GlobalTheory.AbelianPartNorm.norm_eq | (intros; apply GlobalTheory.AbelianPartNorm.norm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInOverValuationRing
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isPolFibre_prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D₀ : Out.DegPre R} {D₁ : Out.DegPre R'} (p : Out.IsPullDeg f D₀ D₁) : IsPolFibre f D₀.P D₁.P (prj p) :=
  ⟨H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_arcIn_over_valuationRing : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (ρ : 𝓞 K₁ →+* Tv.V) (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* Tv.V), (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → (∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (β x))) → ∃ (aw : ArcIn Dw l β Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io a.D₀ aK.D₀) (ψ : aw.D₀.P.A.left ⟶ s.B.A.left), InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict β) pw ∧ InBC io a aK pK ∧ IsPolFibre ρ s.B aw.D₀.P ψ ∧ prj pw ≫ ψ = prj pK ≫ s.φB ∧ TauCan aw.D₀ n' := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s Tv io ρ O _ β b hρ hb
  letI := H.starRing
  obtain ⟨aK, pK, hBC, -⟩ := GlobalTheory.ArcPull.exists_isBC hK.laws.polBaseChange hK.laws.globalFns a io io.injective
  have hB : IsPolFibre (algebraMap (𝓞 K₁) K₁) s.B a.D₀.P s.φB :=
    (isFibreOf_iff_isPolFibre _ _ _ s.B s.toCMPart.xB s.φB).1 s.good.2.2.2.1
  obtain ⟨Pv, ψ, hψ⟩ := exists_isPolFibre hK.laws.polBaseChange ρ s.B
  have hcomp : io.comp (algebraMap (𝓞 K₁) K₁) = (algebraMap Tv.V Tv.Fr).comp ρ :=
    RingHom.ext fun x => (hρ x).symm
  have hχ : IsPolFibre ((algebraMap Tv.V Tv.Fr).comp ρ) s.B aK.D₀.P (prj pK ≫ s.φB) :=
    hcomp ▸ GlobalTheory.CM.EllComp.isPolFibre_comp hB (isPolFibre_prj pK)
  obtain ⟨φ, hφψ, hφ⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift hψ hχ
  obtain ⟨DV, p, rfl, hp, hq⟩ := GlobalTheory.T.exists_degenerationData_extension_over_dvr hK Tv.V Tv.Fr Pv aK.D₀ φ hφ
  obtain rfl : prj p = φ := eq_of_heq hp
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ s.B DV.P ψ hψ.2.1 hψ.2.2 (𝓞 E) s.oa
  have htau : TauCan aK.D₀ n' :=
    (GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult hK K₁ Tv.Fr io a.D₀ aK.D₀ pK n' io.injective a.bimult aK.bimult).1 s.tau
  have hact : ∀ x, (aK.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left := fun x => by
    have h₁ : (aK.oa.onB.act x).left ≫ prj pK = prj pK ≫ (a.oa.onB.act x).left := hBC.act x
    have w := hφ.2.1.1.w
    generalize prj p = u at hφψ w ⊢
    generalize prj pK = u' at hφψ h₁
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hoB, reassoc_of% hφψ, hφψ, reassoc_of% h₁, s.act]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨aw, pw, rfl, hpw, hin, ht⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c O β Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) b
    ((io.comp (algebraMap c.F K₁)).comp β) (aK.restrict β) DV p n' oB (IsFractionRing.injective _ _)
    (RingHom.ext fun x => (hb x).symm) s.n_pos htau hact (fun v => hq _ _ aK.bimult) (fun v => hq _ _ aK.bimult)
  obtain rfl : pw = p := eq_of_heq hpw
  exact ⟨aw, aK, pw, pK, ψ, hin, (inBC_iff_isBC io a aK pK).2 hBC, hψ, hφψ, ht⟩

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberField
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem DescNum.isPolFibre_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D : Out.DegPre R} {D' : Out.DegPre R'} (p : Out.IsPullDeg f D D') : IsPolFibre f D.P D'.P (prj p) :=
  ⟨H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D.P.smoothDim)
    (eSec D'.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem DescNum.epi_of_isPullback_field {K K' : Type} [Field K] [Field K'] (f : K →+* K') {X X' : Scheme.{0}} {φ : X' ⟶ X}
    {s' : X' ⟶ Sp K'} {s : X ⟶ Sp K} (h : IsPullback φ s' s (spMap f)) : Epi φ := by
  letI := f.toAlgebra
  haveI h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat K K')
  haveI h₂ : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  haveI : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip h₁
  haveI : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip h₂
  exact Flat.epi_of_flat_of_surjective φ

theorem exists_arcIn_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  intro hK E _ _ _ H Dw l c K _ _ _ σ₁ σ B aC φ n hσ hn hφ hact htau
  letI := H.starRing
  obtain ⟨oa, hoa, -⟩ := GlobalTheory.LamF.exists_oAct_rosatiConj hK.laws E H (fun _ => rfl) K B
  obtain ⟨P, φP, hP⟩ := exists_isPolFibre hK.laws.polBaseChange (algebraMap (𝓞 K) K) B.pol
  obtain ⟨φ₁, hφ₁, e₁⟩ := PolFibre.cancel hP hφ
  obtain ⟨K₂, _, _, i₂, σ₂, D₂, p₂, ψ₂, hi₂, hψ₂, e₂⟩ :=
    GlobalTheory.T.exists_numberField_normalised_degenerationData hK K σ₁ P aC.D₀ φ₁ n hn hφ₁ aC.even aC.bimult htau
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨K₃, _, _, i₃, σ₃, D₃, q, p₃, hi₃, e₃, hQ⟩ :=
    GlobalTheory.T.exists_numberField_qkPoints_complex_degeneration hK K₂ σ₂ D₂ aC.D₀ p₂ n l.M' hn hM aC.bimult htau.1
  have hψ : IsPolFibre ((i₃.comp i₂).comp (algebraMap (𝓞 K) K)) B.pol D₃.P ((prj q ≫ ψ₂) ≫ φP) :=
    PolFibre.comp hP (PolFibre.comp hψ₂ (DescNum.isPolFibre_of_isPullDeg q))
  have eψ : prj p₃ ≫ (prj q ≫ ψ₂) ≫ φP = φ := by
    rw [← e₁, ← e₂, ← e₃]; simp only [Category.assoc]
  generalize (prj q ≫ ψ₂) ≫ φP = ψ at hψ eψ
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ B.pol D₃.P ψ hψ.2.1 hψ.2.2 (𝓞 E) oa
  letI : Algebra c.F K₃ := ((i₃.comp i₂).comp (algebraMap c.F K)).toAlgebra
  let i : K →ₐ[c.F] K₃ := { i₃.comp i₂ with commutes' := fun _ => rfl }
  have hσ₃ : σ₃.comp (i₃.comp i₂) = σ₁ := by rw [← RingHom.comp_assoc, hi₃, hi₂]
  have hb : σ = σ₃.comp (algebraMap c.F K₃) := by rw [← hσ, ← hσ₃]; rfl
  have hp₃ := (pull_grp p₃).1
  have hcomm : ∀ x, (aC.oa.onB.act x).left ≫ prj p₃ = prj p₃ ≫ (oB.act x).left := fun x => by
    have w : prj p₃ ≫ D₃.P.A.hom = aC.D₀.P.A.hom ≫ spMap σ₃ := hp₃.w
    generalize prj p₃ = π at eψ w
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, eψ, hoB, ← Category.assoc, eψ, hact, hoa]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨a, p', ha, hp', hbc, hta⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c c.F (RingHom.id c.F) K₃ ℂ σ₃ (algebraMap c.F K₃) σ
    aC D₃ p₃ n oB σ₃.injective hb hn htau hcomm (fun v => hQ _ (Nat.dvd_lcm_left _ _) _)
    (fun v => hQ _ (Nat.dvd_lcm_right _ _) _)
  subst ha
  obtain rfl := eq_of_heq hp'
  refine ⟨K₃, inferInstance, inferInstance, inferInstance, i, σ₃, a, p', ψ, hσ₃, hbc, hta, hψ, fun x => ?_⟩
  have hepi : Epi (prj p') := DescNum.epi_of_isPullback_field σ₃ hp₃
  have h := hbc.2.2.2.1 x
  generalize prj p' = π at eψ h hepi
  rw [← cancel_epi π, ← Category.assoc, ← h, Category.assoc, eψ, ← Category.assoc, eψ, hact]

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelianStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearLift_additiveHolomorphic_abelian : ∀ (P P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (RingHom.id ℂ)) φ → ∀ (u : HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (Sp ℂ)) (i : Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ → ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') → IsHolTo Set.univ (fun z => i ≫ (G z).left) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧ (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : epsR ℂ ⟶ P'.A), IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  first | exact @GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | exact GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | (intros; apply GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback <;> assumption)
end

