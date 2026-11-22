import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralPointExtendsModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionJet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Actp

open MvPolynomial in

theorem aug_jetMap {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R)
    (hφ : ∀ i, φ i ∈ orig R κ') :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetMap φ hφ) = jetAug := by
  refine GermD.jet_hom_ext fun i => ?_
  have hk : ∀ P ∈ orig R κ', (aeval (fun _ : κ' => (0 : R))) P = 0 := by
    intro P hP
    have : orig R κ' ≤ RingHom.ker ((aeval (fun _ : κ' => (0 : R)) : MvPolynomial κ' R →ₐ[R] R) : MvPolynomial κ' R →+* R) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      simp [RingHom.mem_ker]
    exact this hP
  have e1 : (jetAug : Jet R κ' m →ₐ[R] R) ((jetMap φ hφ) (Ideal.Quotient.mk _ (X i))) = aeval (fun _ : κ' => (0 : R)) (φ i) := by
    rw [GermD.jetMap_mk, aeval_X]; rfl
  have e2 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (X i)) = 0 := by
    show aeval (fun _ : κ => (0 : R)) (X i) = 0
    simp
  rw [AlgHom.comp_apply, e1, e2, hk _ (hφ i)]

theorem aug_subst {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' R) (z : Jet R κ m) :
    (jetAug : Jet R κ' m →ₐ[R] R) (jetSubstP m φ z) = (jetAug : Jet R κ m →ₐ[R] R) z :=
  DFunLike.congr_fun (aug_jetMap (m := m) (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i)))
    (fun _ => sub_const_mem_orig _)) z

theorem aug_X {R : Type} [CommRing R] {κ : Type} (m : ℕ) (q : κ) :
    (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0
  simp

theorem homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Val

open MvPolynomial

variable {k : Type} [Field k] {d : ℕ}

theorem subst_mk (w : Fin d → k) (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (aeval (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k)) P) := by
  have h : (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k) -
      C (constantCoeff (C (w q.2) * X () : MvPolynomial Unit k))) = fun q => C (w q.2) * X () := by
    funext q
    simp
  rw [CIndFrExp2.jetSubstP_mk, h]

def vW (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) : Fin 1 × Fin d → Jet B Unit p :=
  fun q => algebraMap k _ (w q.2) * dQ B p

theorem aeval_vW_orig (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ)
    (P : MvPolynomial (Fin 1 × Fin d) k) (hP : P ∈ orig k (Fin 1 × Fin d) ^ (p + 1)) :
    aeval (vW w B p) P = 0 := by
  have h1 : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
      MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) P ∈
      Ideal.map ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (orig k (Fin 1 × Fin d) ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h1
  have h2 : Ideal.span (Set.range fun i =>
      ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X i)) ≤ Ideal.span {dQ B p} := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    have : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X q) = vW w B p q := by simp
    beta_reduce
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h3 := Ideal.pow_right_mono h2 (p + 1) h1
  rw [dQ_span_pow] at h3
  exact (Submodule.mem_bot _).1 h3

theorem inL_subst (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    inL (k := k) B p (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P)) =
      aeval (vW w B p) P := by
  rw [subst_mk]
  have e : ∀ Q : MvPolynomial Unit k, inL (k := k) B p (Ideal.Quotient.mk _ Q) = aeval (fun _ => dQ B p) Q := fun _ => rfl
  rw [e, ← AlgHom.comp_apply, comp_aeval]
  have h : (fun q : Fin 1 × Fin d => (aeval (R := k) (fun _ : Unit => dQ B p)) (C (w q.2) * X () : MvPolynomial Unit k)) =
      vW w B p := by
    funext q
    simp [vW]
  exact congrArg (fun u => aeval u P) h

theorem jq_first (w : Fin d → k) (p m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) k) :
    jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      inL (k := k) (Jet k (Fin 1 × Fin d) m) p
        (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ (psTrunc p f))) := by
  have e1 : jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      aeval (vW w (Jet k (Fin 1 × Fin d) m) p) (psTrunc (p + m + 1) f) := by
    show aeval _ (rename _ (psTrunc (p + m + 1) f)) = _
    rw [aeval_rename]
    refine congrArg (fun u => aeval u (psTrunc (p + m + 1) f)) ?_
    funext q
    simp [vW]
  rw [e1, inL_subst, ← sub_eq_zero, ← map_sub]
  exact aeval_vW_orig w _ p _ (CIndFrExp2.psTrunc_sub_mem f (by omega))

end Val

end GlobalTheory.CompanionTheory.Ar.Coc.Actp

namespace GlobalTheory.CompanionTheory.Ar.Coc

open MvPolynomial in

theorem actp_at_point {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hst : ∀ a : 𝓞 E, star a = H.bar a) {X0 : Scheme.{0}} (t : SAB H X0) {k : Type} [Field k] (p : ℕ)
    (x : Sp k ⟶ X0) {d : ℕ} (g : GermAt t x d)
    (σ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p)
    (hσ : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ z) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z)
    (hy : (homAt x σ ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1) (j : Fin d) :
    σ (Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k (Fin 1 × Fin d) p,
      ψ = jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2) := ⟨_, rfl⟩
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p,
      χ₀ = (Algebra.ofId k (Jet k Unit p)).comp (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) := ⟨_, rfl⟩
  have e : g.x p ≫ t.act.act (p : 𝓞 E) = homAt x ψ ≫ g.x p := by
    rw [hψ]; exact g.chart.act p (p : 𝓞 E)
  have h1 : homAt x (σ.comp ψ) ≫ g.x p = 1 := by
    rw [Actp.homAt_comp, Category.assoc, ← e, ← Category.assoc,
      PullbackSections.act_natCast, MonObj.comp_pow, Category.comp_id]
    exact hy
  have h0 : homAt x χ₀ ≫ g.x p = 1 := by
    rw [hχ₀, Actp.homAt_comp, Category.assoc, g.chart.zero p, MonObj.comp_one]
  have a1 : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ (ψ z)) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z := by
    intro z
    rw [hσ, hψ, Actp.aug_subst]
  obtain ⟨χ, -, huniq⟩ := (GlobalTheory.T.formal_germ_dimension_unique E H hst X0 t k x d g).2 Unit p 1 (MonObj.comp_one _)
  have c1 := huniq (σ.comp ψ) ⟨fun q => by rw [AlgHom.comp_apply, a1, Actp.aug_X], h1.symm⟩
  have c0 := huniq χ₀ ⟨fun q => by
    simp only [hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero], h0.symm⟩
  have c : σ.comp ψ = χ₀ := c1.trans c0.symm
  have hc : MvPowerSeries.constantCoeff (g.B.A.act (p : 𝓞 E) j) = 0 := g.B.A.const _ _
  have cc : constantCoeff (psTrunc p (g.B.A.act (p : 𝓞 E) j)) = 0 := by
    have h := GermFun.coeff_psTrunc p (g.B.A.act (p : 𝓞 E) j) 0 (by simp)
    rw [MvPolynomial.constantCoeff_eq, h]
    simpa using hc
  have e' : ψ (Ideal.Quotient.mk _ (X ((0 : Fin 1), j))) = Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j)) := by
    rw [hψ, CIndFrExp2.jetSubstP_mk, aeval_X, cc, map_zero, sub_zero]
  have e2 := DFunLike.congr_fun c (Ideal.Quotient.mk _ (X ((0 : Fin 1), j)))
  rw [AlgHom.comp_apply, e', hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero] at e2
  exact e2

theorem actp_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ j, jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  intro E _ _ _ H _ hst X0 t k _ p _ _ x d g w m hy j
  rw [Actp.jq_first, actp_at_point H hst t p x g _ (fun z => Actp.aug_subst p _ z) hy j, map_zero]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupPointsEquivCommonCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_points_equiv_common_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv | exact GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.LabConst

theorem valAt_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ)) (o : O) (r : R)
    (h : ValAt ξ z (algebraMap O Ω o) r) : r = ρ o := by
  obtain ⟨hsp, t, ht, rfl⟩ := h
  have hg' := ConstReg.genMap_germ_const ξ s hs ⟨centre z, hsp⟩ o
  have ht' := hg.inj ⟨centre z, hsp⟩ (ht.trans hg'.symm)
  rw [ht']
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem const_of_root {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (p : Polynomial ℤ) (hp : p.Monic)
    (hr : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, Polynomial.aeval (f b) p = 0)
    {b b' : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) 1) (hb' : b' ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    f b = f b' := by
  have hne : p.map (Int.castRingHom ℂ) ≠ 0 := (hp.map _).ne_zero
  have hfin : ((p.map (Int.castRingHom ℂ)).rootSet ℂ).Finite := Polynomial.rootSet_finite _ _
  haveI : Finite ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := hfin
  haveI : DiscreteTopology ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := inferInstance
  refine IsPreconnected.constant_of_mapsTo (convex_ball _ _).isPreconnected
    (T := (p.map (Int.castRingHom ℂ)).rootSet ℂ) ⟨inferInstance⟩ hf.continuousOn (fun x hx => ?_) hb hb'
  rw [Polynomial.mem_rootSet]
  refine ⟨hne, ?_⟩
  have h := hr x hx
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq] at h
  rw [Polynomial.coe_aeval_eq_eval]
  exact h

theorem labVal_const_of_isHolPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 R _ jj n ψ hψ
  have hB : ∀ b : Fin n → ℂ, ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ),
      𝔐.LabVal (spMap (ψ b) ≫ jj) id σ ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
    intro b
    obtain ⟨σ, h1, -, -, -, -, h6⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y S Ω K J y 𝔐 ℂ (spMap (ψ b) ≫ jj)
    obtain ⟨h7, h8, -⟩ := h6 (RingHom.id ℂ)
    exact ⟨σ, h1, by simpa using h7, by simpa using h8⟩
  choose σ hσ hc1 hc2 using hB
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = jj ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (jj ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have key : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ∃ r : R, ∀ b, σ b s a = ψ b r := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    refine ⟨ρ (IsIntegralClosure.mk' (𝓞 c.F) _ hint), fun b => ?_⟩
    refine valAt_const 𝔐.ξ 𝔐.tie.gen (𝔐.f ≫ Y.s) 𝔐.cst_over (spMap (ψ b) ≫ jj) ((ψ b).comp ρ) ?_ _ _ ?_
    · rw [Category.assoc, ← hρ]; simp [spMap]
    · have h := hσ b s a
      have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb (id s) a := by
        show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
        rw [IsIntegralClosure.algebraMap_mk']
      rw [he]; exact h
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hconst : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, σ b = σ 0 := by
    intro b hb
    funext s
    refine RingHom.ext fun a => ?_
    obtain ⟨r, hr⟩ := key s a
    obtain ⟨p, hpm, hpe⟩ := NumberField.RingOfIntegers.isIntegral a
    refine const_of_root (fun b => σ b s a) ?_ p hpm ?_ hb h0
    · have : (fun b => σ b s a) = fun b => ψ b r := funext hr
      rw [this]; exact hψ.2 r
    · intro x _
      have h1 : Polynomial.aeval a p = 0 := hpe
      have h2 : Polynomial.aeval (σ x s a) p = (σ x s).toIntAlgHom (Polynomial.aeval a p) :=
        Polynomial.aeval_algHom_apply (σ x s).toIntAlgHom a p
      rw [h2, h1, map_zero]
  refine ⟨σ 0, fun b hb => ?_, hc1 0, hc2 0⟩
  rw [← hconst b hb]
  exact hσ b

end GlobalTheory.CompanionTheory.Ar.Flat.LabConst
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | exact GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_final_estimate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundlePullbackGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_pullback_generator : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_sec_cleared <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem model_point_extends_to_integers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j :=
  @PositivityTheory.Xgn.integral_point_extends_model

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictIntStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_over_restrict_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | exact GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_multiplication_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | exact GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebraStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properness_descends_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsQProjOver p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorLatticeCoordDegreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_lattice_coord_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei] (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ τ, LinearIndependent Ω (s τ)) → (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L) (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω) (T : Ψ → Matrix (Fin m) (Fin m) L), CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g → g ≠ 0 → (∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩) → (∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k') → (∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j)) → (∀ τ, (T τ).det ≠ 0) → (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit.det_frames_size <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TheoremOfCubeSectionValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_section_value : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {T : Over S} (x a : T ⟶ G) (m : ℕ), x ^ m = 1 → ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U), v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen <;> assumption)
end

