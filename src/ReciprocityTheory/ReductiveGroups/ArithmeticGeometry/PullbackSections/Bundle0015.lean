import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0004
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HarmonicValueOfFiniteExtension
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem nab_zCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {k₁ k₂ : ℤ} (h : k₁ = k₂) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k₁ (ptO Xo y.x))) (α : Lt1 Dw →₀ ℕ) :
    nab y k₁ F α = nab y k₂ (zCast Xo.univ.t.G h F) α := by
  subst h
  rfl

theorem vLa_natCast_inv_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {M : ℕ}
    (hM : (M : 𝓞 K) ∉ la.asIdeal) (d : ℕ) : vLa la (((M : K) ^ d)⁻¹) = 0 := by
  have e : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
  have h1 : la.valuation K (M : K) = 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  simp [vLa, map_inv₀, map_pow, h1]

def FFVMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr), P.map io ∈ FFV (Dw := Dw) T a n

def GermTranslateExistence : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ {n : ℕ} (x : Fin n → (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x (x b)) (F b)) →
      ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (g : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)),
        (∀ b, IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
          (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧ ∀ b, IsIntPS Tc (g b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

abbrev IxB (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def eB (Dw : Datum H) : Fin (Fintype.card (IxB Dw)) ≃ IxB Dw := (Fintype.equivFin (IxB Dw)).symm

theorem hS (x : Sp S ⟶ Xo.X) :
    IsGrpPullback ((Over.pullback x).obj Xo.univ.t.G) Xo.univ.t.G x (pullback.fst Xo.univ.t.G.hom x) :=
  isGrpPullback_pullback Xo.univ.t.G x

def uS (y : FrPt Xo c S) (i : Fin (Fintype.card (IxB Dw))) : epsR S ⟶ (Over.pullback y.x).obj Xo.univ.t.G :=
  (push_surj (hS y.x) (tv (fullB y (eB Dw i)))).choose

theorem push_uS (y : FrPt Xo c S) (i : Fin (Fintype.card (IxB Dw))) :
    pushHom (hS y.x) (epsR S) (uS y i) = tv (fullB y (eB Dw i)) :=
  (push_surj (hS y.x) (tv (fullB y (eB Dw i)))).choose_spec

theorem uS_basis (y : FrPt Xo c S) : IsLieBasis (uS y) := by
  refine ⟨fun i => (isTangent_iff (hS y.x) _).2 (by rw [push_uS]; exact tv_mem _), fun w hw => ?_⟩
  have hw' := (isTangent_iff (hS y.x) w).1 hw
  let m : TanM y.x Xo.univ.t.G := mkT _ hw'
  have key : ∀ a : Fin (Fintype.card (IxB Dw)) → S,
      IsLieComb a (uS y) w ↔ m = ∑ k, (a ((eB Dw).symm k)) • fullB y k := by
    intro a
    rw [isLieComb_iff (hS y.x)]
    constructor
    · intro h
      apply tanM_ext
      rw [tv_mkT, h, tv_sum, ← (eB Dw).prod_comp]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply, tv_smul]
      exact congrArg _ (push_uS y i)
    · intro h
      have := congrArg tv h
      rw [tv_mkT, tv_sum, ← (eB Dw).prod_comp] at this
      rw [this]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply, tv_smul]
      exact congrArg _ (push_uS y i).symm
  obtain ⟨A, hA, hAu⟩ := fullB_basis y m
  refine ⟨fun i => A (eB Dw i), (key _).2 (by simpa using hA), fun b hb => ?_⟩
  have := hAu (fun k => b ((eB Dw).symm k)) ((key b).1 hb)
  funext i
  simpa using congrFun this (eB Dw i)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

def NoCommonZeroSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → 4 * DF w + 4 ≤ T.Q.l.M →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
      ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

