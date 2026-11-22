import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProductStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeries
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrixStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeTransform
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

theorem frame_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB P hP
  obtain ⟨w, hw⟩ := Q.bun
  obtain ⟨Qs, hc, hQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main E H hstar X t k p x Q d d' g gB
  have hl := GlobalTheory.T.abelian_quotient_differential_matrix E H hstar X t k p x Q d d' g gB P hP Qs hc hQ
  obtain ⟨lam, hax, hlam⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex.exists_lam E H hstar X t k p x Q d d' g gB w hw Qs hc hQ
  refine ⟨bil lam 1 1, fun a => ?_⟩
  obtain ⟨wL, hwL, hrL⟩ := g.frame.ad a
  obtain ⟨wB, hwB, hrB⟩ := gB.frame.ad a
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio E H hstar X t k p x Q d d' g gB w hw a wL wB hwL hwB
  obtain ⟨h0, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes E H hstar X t k p x Q d d' g gB w hw Qs hc hQ a wL wB hwL hwB hrL hrB u hu
  obtain rfl := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes E H hstar X t k p x Q d g u h0 h1
  have hrel := GlobalTheory.T.abelian_quotient_gauge_relation E H hstar X t k p x Q d d' g gB w hw Qs hc hQ lam hlam a wL wB hwL hwB hrL hrB hu
  rw [← hstar a] at hrel
  obtain ⟨hA, hbA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ k d d' Qs (gB.B.ad a) hc ⟨gB.B.adjoint_zero_fst a, gB.B.adjoint_zero_snd a⟩
  have hadx : AxOne (g.B.ad a) := ⟨g.B.adjoint_zero_fst a, g.B.adjoint_zero_snd a⟩
  have hcs : ∀ (b : 𝓞 E) (i : Fin d), MvPowerSeries.constantCoeff (g.B.A.act b i) = 0 := fun b i => g.B.A.const b i
  have hp0 : ∀ i : Fin d, MvPowerSeries.constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => by simp [pt]
  have hp2 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (pt k (n := 2) d j i) = 0 := fun j i => by simp [pt]
  obtain ⟨-, -, -, hT, hbT, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (pt k d 0) (g.B.A.act (star a)) hax hax hp0 (hcs _)
  obtain ⟨-, -, -, hS, hbS, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (g.B.A.act a) (pt k d 0) hax hax (hcs _) hp0
  rw [germ_comp1_zero_point_left _ (hp2 0)] at hT hbT
  rw [germ_comp1_zero_point_left _ (hp2 1)] at hS hbS
  obtain ⟨-, -, e1, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d (subQ Qs (gB.B.ad a)) _ (pt k d 0) (pt k d 0) hA hT hp0 hp0
  obtain ⟨-, -, e2, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d _ (g.B.ad a) (pt k d 0) (pt k d 0) hS hadx hp0 hp0
  have h := congrArg (fun f => bil f 1 1) hrel
  beta_reduce at h
  rw [e1, e2, hbT, hbS, hbA, hl, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  change _ + (rho g.B a).transpose * _ - _ * rho g.B (star a) = _
  change _ + bil lam 1 1 * rho g.B (star a) = (rho g.B a).transpose * bil lam 1 1 + _ at h
  rw [eq_sub_of_add_eq h]
  abel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
