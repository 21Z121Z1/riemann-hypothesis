import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Group

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {i d : ℕ}

def pairDet (l w : Fin i → Fin d → C) : C := (Matrix.of fun a b : Fin i => ∑ e, l b e * w a e).det

def IsFrameOf (v : AddValuation C (WithTop ℝ)) (u w : Fin i → Fin d → C) : Prop :=
  IsSatFrame v w ∧ ∀ a, w a ∈ Submodule.span C (Set.range u)

def HasChars (G : LogFGL v d) (u : Fin i → Fin d → C) (r : EReal) : Prop :=
  ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧
    ∀ w : Fin i → Fin d → C, IsFrameOf v u w → toE (v (pairDet l w)) ≤ r

theorem isFrameOf_self {u : Fin i → Fin d → C} (hu : IsSatFrame v u) : IsFrameOf v u u :=
  ⟨hu, fun a => Submodule.subset_span ⟨a, rfl⟩⟩

theorem v_pairDet_eq {u w : Fin i → Fin d → C} (hu : IsSatFrame v u) (hw : IsFrameOf v u w)
    (l : Fin i → Fin d → C) : v (pairDet l w) = v (pairDet l u) := by
  choose M hM using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (hw.2 a)
  have hwe : ∀ a e, w a e = ∑ k, M a k * u k e := fun a e => by
    rw [← hM a]; simp [Finset.sum_apply]
  have hmin : ∀ r : Fin i → Fin d, (Matrix.of fun a b => w a (r b)).det =
      (Matrix.of M).det * (Matrix.of fun a b => u a (r b)).det := fun r => by
    rw [← Matrix.det_mul]; congr 1; ext a b; simp [Matrix.mul_apply, hwe]
  have hint : ∀ (x : Fin i → Fin d → C), (∀ a e, IsIntV v (x a e)) → ∀ r : Fin i → Fin d,
      0 ≤ v (Matrix.of fun a b => x a (r b)).det := fun x hx r => by
    rw [Matrix.det_apply']
    refine AddValuation.map_le_sum v fun σ _ => ?_
    rw [AddValuation.map_mul]
    refine add_nonneg ?_ ?_
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · refine Finset.prod_induction _ (fun z => 0 ≤ v z) (fun a b ha hb => ?_) (by simp) fun k _ => hx _ _
      rw [AddValuation.map_mul]; exact add_nonneg ha hb
  obtain ⟨r, hr⟩ := hu.2
  obtain ⟨r', hr'⟩ := hw.1.2
  have h1 : 0 ≤ v (Matrix.of M).det := by
    have := hint w hw.1.1 r
    rwa [hmin, AddValuation.map_mul, hr, add_zero] at this
  have h2 : v (Matrix.of M).det ≤ 0 := by
    rw [hmin, AddValuation.map_mul] at hr'
    exact hr' ▸ le_add_of_nonneg_right (hint u hu.1 r')
  have h3 : pairDet l w = (Matrix.of M).det * pairDet l u := by
    unfold pairDet
    rw [← Matrix.det_mul]; congr 1; ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, hwe, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h3, AddValuation.map_mul, le_antisymm h2 h1, zero_add]

theorem hasChars_iff {G : LogFGL v d} {u : Fin i → Fin d → C} (hu : IsSatFrame v u) (r : EReal) :
    HasChars G u r ↔ ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧ toE (v (pairDet l u)) ≤ r :=
  exists_congr fun l => and_congr_right fun _ =>
    ⟨fun h => h u (isFrameOf_self hu), fun h w hw => by rwa [v_pairDet_eq hu hw]⟩

end Group

section Prime

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop := ¬ (p : ℤ) ∣ discr E

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

variable {H : Host E} {l : Level H} (c : Coeff l) {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime]
  (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

def vd_vp (τ : E →+* ℂ) : EReal :=
  ⨅ a ∈ differentIdeal ℤ (𝓞 E), toE (vX_vp X (embX c io X τ a))

end Prime

def BigBlockChars : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p) (f : Lt1 Dw), f.1 (H.rt : E) = H.rt0 →
      (p ≠ 2 → UnramIn E p → SplitInK H p →
        HasChars (fgl Ch X) (frame Ch X f) (((Dw.q : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal)) ∧
      (p ≠ 2 → UnramIn E p → InertInK H p →
        HasChars (fgl Ch X) (frame Ch X f)
          (((Dw.q : ℝ) / ((p : ℝ) - 1) +
            (((Dw.p + Dw.q : ℕ) : ℝ) - 2 * (Dw.q : ℝ)) * (p : ℝ) / ((p : ℝ) ^ 2 - 1) : ℝ) : EReal)) ∧
      (p = 2 ∨ SplitInK H p →
        HasChars (fgl Ch X) (frame Ch X f)
          (min (((rk f : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal)
            (((Dw.q : ℝ) : EReal) * ((((1 : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal) + vd_vp c io X f.1))))

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime] {T : CDVR} {io : c.F →+* T.Fr}
    {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) :
    IsFrameOf (vX_vp X) (frame Ch X f) (frame Ch X f) :=
  isFrameOf_self (isSatFrame_frame Ch X f)

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : Dw.mult τ + Dw.q = Dw.p + Dw.q := by
  simp [Datum.mult, h]

example : ¬ IsSquare (-((7 : ℕ) : ZMod 3)) ∧ IsSquare (-((7 : ℕ) : ZMod 11)) := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∉ w.asIdeal ^ 2

def quadK (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {(H.rt : E)}

def InertK (H : Host E) (p : ℕ) : Prop := (Ideal.span {(p : 𝓞 (quadK H))}).IsPrime

def SplitK (H : Host E) (p : ℕ) : Prop :=
  ∃ P Q : Ideal (𝓞 (quadK H)), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ P * Q = Ideal.span {(p : 𝓞 (quadK H))}

def boundAll (p i k : ℕ) : ℝ := (i : ℝ) * k / ((p : ℝ) - 1)

def boundInert (p j' i k : ℕ) : ℝ := 2 * (i : ℝ) * k / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * (j' : ℝ) * k / ((p : ℝ) - 1)

def boundSplit (p j' k : ℕ) : ℝ := (k : ℝ) * j' / ((p : ℝ) - 1)

def upperInert (p N j' k : ℕ) : ℝ :=
  (k : ℝ) * ((j' : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j') * p / ((p : ℝ) ^ 2 - 1))

def lowerInert (p i k cr : ℕ) : ℝ :=
  (i : ℝ) * k * p / ((p : ℝ) ^ 2 - 1) - (k : ℝ) * cr * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p k + 1)

def boundFine (p N j' i k : ℕ) : ℝ :=
  (k : ℝ) * ((N : ℝ) - 2 * j' - i) * p / ((p : ℝ) ^ 2 - 1) +
    (k : ℝ) * j' * (3 + 1 / 2 * Real.logb p k) / ((p : ℝ) - 1) + (i : ℝ) ^ 2 * (Real.logb p k + 1)

variable {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
  {p : ℕ} [Fact p.Prime]

def AtEvery (la : PointsOfFlagModel.abelian₂ p c) (Q : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, Q T io y

def kap {T : CDVR} (X : ValExt T p) (i k : ℕ) : EReal := content (vX_vp X) (detPow X.C i k)

variable {Xo c} in

def htColength {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)
    (f : Lt1 Dw) : EReal :=
  ⨅ (lv : Fin (rk f) → Fin (chD Ch.ch) → X.C) (_ : ∀ b, IsCharLog (fgl Ch X) (lv b)),
    toE (vX_vp X (Matrix.det (Matrix.of fun a b : Fin (rk f) => ∑ e, lv b e * frame Ch X f a e)))

def OscLe (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (b : ℝ) : Prop :=
  AtEvery Xo c la fun _ _ y => AtEvery Xo c la fun _ _ η => nuFac p y f k ≤ nuFac p η f k + (b : EReal)

def ClauseAll (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T _ y => 0 ≤ nuFac p y f k ∧ ∀ X : ValExt T p,
    nuFac p y f k ≤ kap X (rk f) k ∧ kap X (rk f) k ≤ (boundAll p (rk f) k : EReal)) ∧
  OscLe Xo c la f k (boundAll p (rk f) k)

def ClauseInert (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T _ y => ∀ X : ValExt T p,
    kap X (rk f) k ≤ nuFac p y f k + (boundInert p Dw.q (rk f) k : EReal)) ∧
  OscLe Xo c la f k (boundInert p Dw.q (rk f) k)

def ClauseSplit (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun T io y =>
    (∀ (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      nuFacC Ch X f k ≤ ((k : ℝ) : EReal) * htColength Ch X f ∧
        htColength Ch X f ≤ (boundSplit p Dw.q 1 : EReal)) ∧
    nuFac p y f k ≤ (boundSplit p Dw.q k : EReal)) ∧
  OscLe Xo c la f k (boundSplit p Dw.q k)

def ClauseFine (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) : Prop :=
  (AtEvery Xo c la fun _ _ η => ∃ cr : ℕ, cr ≤ rk f ∧ (cr : ℝ) ≤ (Dw.q : ℝ) * (3 / 2 + 1 / 2 * Real.logb p k) ∧
    (lowerInert p (rk f) k cr : EReal) ≤ nuFac p η f k) ∧
  (AtEvery Xo c la fun _ _ y => nuFac p y f k ≤ (upperInert p (Dw.p + Dw.q) Dw.q k : EReal)) ∧
  OscLe Xo c la f k (boundFine p (Dw.p + Dw.q) Dw.q (rk f) k)

def FactorBoundsAt (p : ℕ) [Fact p.Prime] : Prop :=
  UnramIn E p → ∀ (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ),
    ClauseAll Xo c la f k ∧
    (InPsi H f.1 → InertK H p → ClauseInert Xo c la f k) ∧
    (InPsi H f.1 → Odd p → SplitK H p → ClauseSplit Xo c la f k) ∧
    (InPsi H f.1 → Odd p → InertK H p → 1 ≤ k → ClauseFine Xo c la f k)

def FactorBounds : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) → ∀ (p : ℕ) [Fact p.Prime], FactorBoundsAt Xo c p

def FactorDepthBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], FactorBounds Xo c

example : boundFine 3 1 0 1 1 = 1 ∧ upperInert 3 1 0 1 = 3 / 8 := by
  constructor
  · simp [boundFine]
  · norm_num [upperInert]

end GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Col (cx : Lt1 Dw → ℕ) : Type := Σ f : {f : Lt1 Dw // cx f ≠ 0}, Fin (rk f.1)

abbrev Let (cx : Lt1 Dw → ℕ) : Type := Σ b : Col cx, Fin (rk b.1.1)

def polyH (C : Type) [Field C] (cx : Lt1 Dw → ℕ) : MvPolynomial (Let cx) C :=
  ∏ f : {f : Lt1 Dw // cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
    (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Let cx)) (detPow C (rk f.1) (cx f.1))

def blockCols (cx : Lt1 Dw → ℕ) : ℕ := ∑ f : {f : Lt1 Dw // cx f ≠ 0}, 2 * rk f.1

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
  {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ}
  (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)

def expH : (Σ _ : Col cx, Fin (chD Ch.ch)) → MvPowerSeries (Let cx) X.C :=
  expAlong (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1)

def colPt : Fin n × Fin (chD Ch.ch) → MvPowerSeries (Let cx) X.C := fun q =>
  subst (fun e : Fin (chD Ch.ch) => ∑ ℓ : Let cx,
    (jX X (B ℓ.1.1.1 ℓ.1.2 q.1) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
    (expOf (fgl Ch X) q.2)

def nuH_vp : EReal := depth (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1) (polyH X.C cx)

def nabX (k : ℕ) (g : PS X.C n (chD Ch.ch)) : X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra ℚ X.C := DivisionRing.toRatAlgebra
  nabValN Ch.ch.B X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))

def nuLocX_vp (k : ℕ) : EReal :=
  ⨅ g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g}, toE (vX_vp X (nabX Ch X cx B k g.1))

def Restricts (g : PS X.C n (chD Ch.ch)) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) : Prop :=
  subst (colPt Ch X cx B) g = subst (expH Ch X cx) f

def Trivial : Prop :=
  (∀ g, MvIsInt (vX_vp X) g → ∃ f, MvIsInt (vX_vp X) f ∧ Restricts Ch X cx B g f) ∧
  (∀ f, MvIsInt (vX_vp X) f → ∃ g, MvIsInt (vX_vp X) g ∧ Restricts Ch X cx B g f) ∧
  ∃ U : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) U ∧ constantCoeff U = 1 ∧
    ∀ (k : ℕ) g f, Restricts Ch X cx B g f →
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) (f * U ^ k))

def DepthEq : Prop :=
  nuH_vp Ch X cx = nuP p y cx ∧
  (∀ k : ℕ, nuLocX_vp Ch X cx B k = nuP p y cx) ∧
  (∀ k e : ℕ, vV T.V (p : T.Fr) = e → nuLocOf Ch e k (polyT B cx) = nuP p y cx) ∧
  0 ≤ nuP p y cx

end Chart

variable (Dw c) in

def ColsExist (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (cx : Lt1 Dw → ℕ) (n : ℕ), blockCols cx ≤ n →
    ∃ x : ℕ → ∀ f : Lt1 Dw, Fin (rk f) → Fin n → 𝓞 E,
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∃ B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V, IsCols c T io p cx B ∧
          ∀ (N : ℕ) (f : Lt1 Dw) (b : Fin (rk f)) (j : Fin n), ∃ z : T.V,
            io (embK c f.1 (x N f b j)) = algebraMap T.V T.Fr (B f b j + (p : T.V) ^ N * z)

variable (Dw c) in

def ColsHarmonic (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) →
      ∀ (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p (gap Dw a) B →
        polyT B (gap Dw a) ∈ FFV (Dw := Dw) T a n

variable (Xo c) in

def LocalDepth (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ)
      (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B →
      Trivial Ch X cx B ∧ DepthEq Ch X cx B

variable (Xo c) in

def ChoiceOfP : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) → ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c),
    ColsExist Dw c p la ∧ ColsHarmonic Dw c p la ∧ LocalDepth Xo c p la

example {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c} (h : LocalDepth Xo c p la) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la.1 T.V io e) {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {a : (E →+* ℂ) × ℕ → ℕ}
    (ha : ∀ τ, Antitone fun i => a (τ, i)) {n : ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V}
    (hB : IsCols c T io p (gap Dw a) B) (k ep : ℕ) (hp : vV T.V (p : T.Fr) = ep) :
    nuLocC Ch ep k a n ≤ nuP p y (gap Dw a) := by
  obtain ⟨X⟩ := nonempty_valExt_of_overLa (p := p) la ho
  rw [← (h T io e ho y Ch X _ n B hB).2.2.2.1 k ep hp]
  exact nuLocC_le_nuLocOf Ch ep k ha hB

omit [StarRing (𝓞 E)] in

example (C : Type) [Field C] : polyH (Dw := Dw) C (fun _ => 0) = 1 := by
  have : IsEmpty {f : Lt1 Dw // (fun _ => 0 : Lt1 Dw → ℕ) f ≠ 0} := ⟨fun f => f.2 rfl⟩
  simp [polyH]

end GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SplitQuadraticMinSums
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def vDiff_vp (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℝ :=
  (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) : ℝ) /
    (multiplicity w.asIdeal (Ideal.span {(p : 𝓞 E)}) : ℝ)

def SplitAt (H : Host E) (p : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal

def SplitQuad (H : Host E) (p : ℕ) : Prop :=
  (p = 2 ∧ H.d % 8 = 7) ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)

def RamifiedPrimes (H : Host E) (S : Finset ℕ) (q₁ : ℕ) : Prop :=
  IsAbelianGalois ℚ E ∧ q₁.Prime ∧ 11 ≤ q₁ ∧ q₁ % 8 = 3 ∧ q₁ ≠ H.d ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S ∨ p = q₁ ∨ p = H.d) ∧
    (2 ∈ S ∧ ∀ p ∈ S, p.Prime ∧ SplitQuad H p ∧ SplitAt H p) ∧ SplitAt H q₁ ∧ SplitAt H H.d

variable {H : Host E} {Dw : Datum H}

def IsBig (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ k ≤ rk f + 1

def IsSpread (k : ℕ) (f : Lt1 Dw) : Prop := InPsi H f.1 ∧ rk f + 2 ≤ k

def IsSmall (f : Lt1 Dw) : Prop := ¬ InPsi H f.1

theorem not_isBig_iff (k : ℕ) (f : Lt1 Dw) : ¬ IsBig k f ↔ IsSmall f ∨ IsSpread k f := by
  unfold IsBig IsSmall IsSpread
  by_cases h : InPsi H f.1
  · simp only [h, true_and, not_true, false_or]; omega
  · simp [h]

open Classical in

def sumBig (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ := ∑ f ∈ Finset.univ.filter (IsBig k), cx f

open Classical in

def sumSmallSpread (k : ℕ) (cx : Lt1 Dw → ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f => IsSmall f ∨ IsSpread k f), rk f * cx f

def boundTwo_vp (k : ℕ) (vd : ℝ) (cx : Lt1 Dw → ℕ) : ℝ :=
  (Dw.q : ℝ) * (1 + vd) * (sumBig k cx : ℝ) + (sumSmallSpread k cx : ℝ)

def boundSmall_vp (p k : ℕ) (vd : ℝ) (cx : Lt1 Dw → ℕ) : ℝ :=
  (Dw.q : ℝ) * (1 / ((p : ℝ) - 1) + vd) * (sumBig k cx : ℝ) + 1 / ((p : ℝ) - 1) * (sumSmallSpread k cx : ℝ)

def boundDeg_vp (p : ℕ) (cx : Lt1 Dw → ℕ) : ℝ := (degP cx : ℝ) / ((p : ℝ) - 1)

section Place

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime]

def DepthBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (B : ℝ) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    0 ≤ nuP p y cx ∧ nuP p y cx ≤ (B : EReal)

def OscBelow (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (B : ℝ) : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F), PointsOfFlagModel.BaseAt la.1 β → ∀ (Y : Model Xo c β) (Z : Comp Xo c),
    GenEx Y Z la.1 →
      eLoc Y Z la cx ≤ nuPSup (fun _ _ y => OnComp Z y ∧ y.IsAlg) la cx ∧
      nuPSup (fun _ _ y => OnComp Z y ∧ y.IsAlg) la cx ≤ (B : EReal) ∧
      eLoc Y Z la cx ≤ (B : EReal)

end Place

def UnscaledDepthBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Finset ℕ) (q₁ : ℕ), RamifiedPrimes H S q₁ →
    ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (Dw : Datum H) (k j : ℕ), 3 ≤ k → 1 ≤ j → Dw.p + 1 = k + j →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (cx : Lt1 Dw → ℕ),
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (la : PointsOfFlagModel.abelian₂ p c) (w : HeightOneSpectrum (𝓞 E)),
        (p : 𝓞 E) ∈ w.asIdeal →
        DepthBetween Xo c la cx (boundSmall_vp p k (vDiff_vp p w) cx) ∧
        OscBelow Xo c la cx (boundSmall_vp p k (vDiff_vp p w) cx)) ∧
      ∀ (p : ℕ) [Fact p.Prime], p = q₁ ∨ p = H.d → ∀ la : PointsOfFlagModel.abelian₂ p c,
        DepthBetween Xo c la cx (boundDeg_vp p cx) ∧ OscBelow Xo c la cx (boundDeg_vp p cx)

end GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification
end
end

