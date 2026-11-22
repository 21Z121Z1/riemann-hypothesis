import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BalOf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem bal_of {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m) (B A Ab : Fin d → Fin d → S)
    (h2 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2) (h3 : P - 1 - bil B ∈ Io S (Fin 2 × Fin d) ^ 3)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A (0 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab (1 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1)) :
    Matrix.transpose (Matrix.of A) * Matrix.of B = Matrix.of B * Matrix.of Ab := by
  set W := P - 1 with hWdef
  set h := bil B with hhdef
  have hhI : h ∈ Io S (Fin 2 × Fin d) ^ 2 := bil_mem B
  have hh : h.IsHomogeneous 2 := bil_hom B
  have hmj : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ (m + 1) → p ∈ Io S _ ^ (2 + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ 2 → p ∈ Io S _ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), ev2 P u v = 1 + ev2 W u v := by
    intro u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) → (∀ i, v i ∈ Io S _) →
      ev2 W u v - ev2 h u v ∈ Io S _ ^ (2 + 1) := by
    intro u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ h3
  have hRep : ∀ (u v u' v' : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) →
      (∀ i, v i ∈ Io S _) → (∀ i, u' i ∈ Io S _) → (∀ i, v' i ∈ Io S _) → (∀ i, u i - u' i ∈ Io S _ ^ 2) →
      (∀ i, v i - v' i ∈ Io S _ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S _ ^ (2 + 1) := by
    intro u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) 2 h hhI
  have hx : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) := fun k i => xs_mem k i
  have hl : ∀ (M : Fin d → Fin d → S) (k : Fin 2) (i : Fin d), lin M k i ∈ Io S (Fin 2 × Fin d) :=
    fun M k i => lin_mem M k i
  have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
  have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
  have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
    have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈
        Io S _ ^ (2 + 1) := by
      have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
          (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
          (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
          (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
          (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
        rw [hPW, hPW]; ring
      rw [e]
      exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
        (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
        (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
    exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
      ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
  ext i0 l0
  have hc := congrArg (coeff (sil i0 l0)) hb1
  rw [hhdef, eval_pair_bilinear, eval_pair_bilinear, coeff_linL, coeff_linR] at hc
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact hc

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace BoxTuple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

end BoxTuple

open BoxTuple

def BoxAssemblySt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E) (n₁ n₂ : ℕ)
    (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∃ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (pD₁ : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA₁ : IsPowPolAV A₁ P.A 1) (pG₁ : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU₁ : UnifPowOf3 pD₁ pA₁ pG₁ U₁ P.U)
    (_ : Module (𝓞 E) D₁.toPre.X) (oD₁ : D₁.toPre.OAct (𝓞 E))
    (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (pD₂ : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA₂ : IsPowPolAV A₂ P.A n₂) (pG₂ : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU₂ : UnifPowOf3 pD₂ pA₂ pG₂ U₂ P.U)
    (_ : Module (𝓞 E) D₂.toPre.X) (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD₁.xe (a • x) i = a • pD₁.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD₁.pw.pr i = pD₁.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD₂.xe (a • x) i = a • pD₂.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD₂.pw.pr i = pD₂.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    ∀ (s₁ : Fin n₁ → Fam D₁.toPre F g') (s₂₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (p₁ : Fin n₁ → QkPt D₁.toPre F (g' * g))
      (w₁ : ∀ i, LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F (p₁ i).g.b) (DegPre.lineε (g' * g))))
      (ζ₁ : Fin n₁ → F) (x₁ : Fin n₁ → (TFK (R := T.V) F ⟶ A₁.A)) (t₀₁ t₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (σ₁ : Fin n₁ → U₁.toUnifPre.SecGF F (g' * g)) (h₁ : Fin n₁ → PS F 1 (chD C.ch)),
      (∀ i, BoxTup C P Q F v g g' π pG₁ PU₁ oD₁ (s₁ i) (s₂₁ i) (p₁ i) (w₁ i) (ζ₁ i) (x₁ i) (t₀₁ i) (t₁ i)
        (σ₁ i) (h₁ i)) →
    ∀ (sb : Fam D₂.toPre F g') (s₂b : Fam D₂.toPre F (g' * g)) (pb : QkPt D₂.toPre F (g' * g))
      (wb : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F pb.g.b) (DegPre.lineε (g' * g))))
      (ζb : F) (xb : TFK (R := T.V) F ⟶ A₂.A) (t₀b tb : Fam D₂.toPre F (g' * g))
      (σb : U₂.toUnifPre.SecGF F (g' * g)) (hb : PS F n₂ (chD C.ch)),
      BoxTup C P Q F v g g' π pG₂ PU₂ oD₂ sb s₂b pb wb ζb xb t₀b tb σb hb →
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)),
      BoxTup C P Q F v g g' π pG PU oD' s s₂ p w ζ x t₀ t σ' h ∧
      h = (∏ i : Fin n₁, MvPowerSeries.rename
            (fun q : Fin 1 × Fin (chD C.ch) => ((Fin.castAdd n₂ i, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) (h₁ i)) *
          MvPowerSeries.rename
            (fun q : Fin n₂ × Fin (chD C.ch) => ((Fin.natAdd n₁ q.1, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) hb ∧
      (∀ i : Fin n₁, x ≫ pA.pr (Fin.castAdd n₂ i) = x₁ i ≫ pA₁.pr 0) ∧
      ∀ i : Fin n₂, x ≫ pA.pr (Fin.natAdd n₁ i) = xb ≫ pA₂.pr i

def SecondFrameStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n₂ : ℕ) (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) [GrpObj G₂] [IsCommMonObj G₂] (pD : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA : IsPowPolAV A₂ P.A n₂) (pG : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU : UnifPowOf3 pD pA pG U₂ P.U)
    [Module (𝓞 E) D₂.toPre.X] (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (m : (E →+* ℂ) → ℕ → ℕ) (D : ℕ),
    (∀ τ s, m τ s ≠ 0 → ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) →
      1 ≤ s ∧ s ≤ Dw.mult τ ∧ s ≤ n₂) →
    degOf Dw m ≤ D → 4 * D + 4 ≤ g' → (D : ℝ) * M0 < g' →
    letI := io.toAlgebra
    ∃ (s : Fam D₂.toPre F g') (s₂ : Fam D₂.toPre F (g' * g)) (p : QkPt D₂.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A₂.A) (t₀ t : Fam D₂.toPre F (g' * g))
      (σ' : U₂.toUnifPre.SecGF F (g' * g)) (h : PS F n₂ (chD C.ch)) (ρ₂ : ℚ),
      BoxTup C P Q F v g g' π pG PU oD₂ s s₂ p w ζ x t₀ t σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw n₂ => ℓ.2.2) (fun (ℓ : LtN Dw n₂) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂ id)) =
        (ρ₂ : WithTop ℚ) ∧
      (ρ₂ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / g'

def DirOntoSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (g : ℕ), g.Prime →
    ¬ IsUnit ((g : ℕ) : T.V) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ∀ t : Lt1 Dw → T.V, ∃ a : Fin (chD C.ch) → T.V, ∀ ℓ, ∑ j, a j * C.uvecT ℓ j = t ℓ

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem push_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a b : T ⟶ G'}
    (e : pushHom h T a = pushHom h T b) : a = b := by
  have e1 : a.left ≫ φ = b.left ≫ φ := congrArg (fun z => z.left) e
  have e2 : a.left ≫ G'.hom = b.left ≫ G'.hom := by
    rw [Over.w a, Over.w b]
  exact Over.OverMorphism.ext (h.1.hom_ext e1 e2)

theorem jetCoef_copy {V K : Type} [CommRing V] [CommRing K] (f : V →+* K) (d m n : ℕ) (i : Fin n) :
    (jetCoef f (Fin n × Fin d) m).comp ((jetCopy (S := V) d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
      Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) =
    ((jetCopy (S := K) d m i : Jet K (Fin 1 × Fin d) m →ₐ[K] Jet K (Fin n × Fin d) m) :
      Jet K (Fin 1 × Fin d) m →+* Jet K (Fin n × Fin d) m).comp (jetCoef f (Fin 1 × Fin d) m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.C r))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.C r)))
    simp
  · intro q
    show Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.map f (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.X q))) =
      Ideal.Quotient.mk (orig K (Fin n × Fin d) ^ (m + 1))
        (MvPolynomial.bind₁ (fun p : Fin 1 × Fin d => MvPolynomial.X (i, p.2))
          (MvPolynomial.map f (MvPolynomial.X q)))
    simp

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

def U2 (m : ℕ) : Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ jOG (𝟙 (Sp T.V)) d m 2 :=
  Over.homMk (spMap (jc (d := d) 2 m)) (by
    show spMap (jc (d := d) 2 m) ≫ spMap (algebraMap T.V (Jet T.V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
      (spMap (algebraMap T.Fr (Jet T.Fr (Fin 2 × Fin d) m)) ≫ 𝟙 _) ≫ spMap (algebraMap T.V T.Fr)
    rw [Category.comp_id, Category.comp_id, spMap_comp', spMap_comp', jetCoef_alg])

theorem push_jpt (m : ℕ) (i : Fin 2) :
    pushHom I.m2.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) = U2 (d := d) m ≫ jptG I.G (𝟙 (Sp T.V)) d xT m i := by
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_copy]

theorem xP_law (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) T.V) (m : ℕ)
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (FT p.2)) ≫ xT m =
      jptG I.G (𝟙 (Sp T.V)) d xT m (0 : Fin 2) * jptG I.G (𝟙 (Sp T.V)) d xT m (1 : Fin 2)) :
    Formalism.L2.Pj.homAt (𝟙 (Sp T.Fr)) (jetSubstP m fun p : Fin 1 × Fin d =>
              MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (FT p.2))) ≫ xP I xT m =
      jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (0 : Fin 2) * jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m (1 : Fin 2) := by
  apply push_inj I.m2.cart
  rw [map_mul, push_jpt, push_jpt, ← MonObj.comp_mul, ← hl]
  apply Over.OverMorphism.ext
  show (spMap _ ≫ xL I xT m) ≫ I.m2.φ = spMap (jc (d := d) 2 m) ≫ spMap _ ≫ (xT m).left
  rw [Category.assoc, xL_fst, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', jetCoef_substP]

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ColumnValueStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def OneColumnStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
    letI := io.toAlgebra
    ∃ (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g)) (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀

def ColumnValueStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (u : PS F 1 (chD C.ch)), (∀ e, 0 ≤ v (MvPowerSeries.coeff e u)) → MvPowerSeries.constantCoeff u = 1 →
    ev (n := 2) ![fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)] u =
      ev (n := 2) ![pt F (chD C.ch) 0] u * ev (n := 2) ![pt F (chD C.ch) 1] u →
    letI := io.toAlgebra
    ∃ (x : TFK (R := T.V) F ⟶ A₁.A) (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g))
      (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀ ∧
      ∀ Pv : MvPolynomial (LtN Dw 1) F, (∀ mm, 0 ≤ v (Pv.coeff mm)) →
        (∀ ℓ ∈ Pv.vars, 0 < v (algebraMap T.Fr F (io (embK c ℓ.1 (star π))))) → Pv.totalDegree < g →
        v c₀ + v ((g : ℕ) : F) ≤
          v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
              (fun ℓ : LtN Dw 1 => ℓ.2.2) (fun (ℓ : LtN Dw 1) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) Pv -
            MvPolynomial.eval (fun ℓ : LtN Dw 1 => MvPowerSeries.constantCoeff
                (DofN (fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)) (0 : Fin 1)
                  (fun j => algebraMap T.V F (C.uvecT ⟨ℓ.1, ℓ.2.1⟩ j)) u)) Pv *
              MvPowerSeries.constantCoeff h)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def PowOActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre P.D.toPre n),
    letI := H.starRing
    ∃ M : Module (𝓞 E) D'.toPre.X,
      letI := M
      ∃ oD' : D'.toPre.OAct (𝓞 E),
        (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧
        ∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem intChart_of_cut (hA : ChartDataGSt) (hB : FrameSt) (hC : FBIdSt) (hGF : GlobalFnsSt) :
    IntChartStatement := by
  intro E _ _ _ H V _ _ _ hc t hprop κ _ tg htan hbas _ hstar
  obtain ⟨d, G, A, uvec, x, hd, hu, hch⟩ := hA E H (Sp V) t V (𝟙 (Sp V)) tg htan hbas
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    hB E H (Sp V) t V (𝟙 (Sp V)) d G A κ tg uvec x hch
  have hPow := globalFnsDvr_of_globalFns hGF E H V hc t hprop
  obtain ⟨hax, hr⟩ := hC E H (Sp V) t hPow hstar V (𝟙 (Sp V)) d G A κ tg uvec x e ph1 ph2 sy ad hch hfr hfa had
  refine ⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, hd, hu, hch, hfr, hpr, htr, hrig, fun k F => ?_⟩
  exact germSt_holds E H (Sp V) t V (𝟙 (Sp V)) d G.F A.act κ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k F

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

