import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
import Formalism.LocalToGlobal.CharacterGerms.Bundle0008

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace IndependenceBoundPlain

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)

def PlainCoefficientIdentity (H : ∀ g, X.CartHyp V g) : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)

theorem independence_bound_raw [IsAlgClosed C] [NeZero d] (hrk : X.RankHyp) (H : ∀ g, X.CartHyp V g) (hR2 : RawChart.RankMaximalCondition H)
    (hcoef : PlainCoefficientIdentity X H) : RawChart.IndependenceBoundCondition H := by
  intro hAlt g a hbig N w x hg hV hind
  have key : ∀ g' : Fin 2, X.big g' a → X.big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ X.big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // X.ty (1 - g) q = a + 2} = X.j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := hcoef hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  have hspan : ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * M (σ r).1 q) := by
    intro w x hg hV
    obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
    refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
    have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
      rw [← Finset.sum_filter_of_ne (p := fun q' => X.ty (1 - g) q' = a + 2)
        (fun q' _ hne => by
          by_contra hq
          exact hne (by rw [hsupp q' hq, zero_mul]))]
      rw [Finset.sum_subtype (Finset.univ.filter fun q' => X.ty (1 - g) q' = a + 2)
        (p := fun q' => X.ty (1 - g) q' = a + 2) (fun q' => by simp)]
      exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
    rw [← hsum]
    exact hc1 q
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) (fun r => M (σ r).1) hspan
    N w x hg hV hind

end IndependenceBoundPlain

section Closed

theorem independence_bound_all_charts_of_coefficient_identity (h : CoefficientIdentityCondition) : IndependenceBoundAllCharts := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.raw p) hrk H hR2 (h C V O dd Y d I p hrk H)

def CoefficientIdentitySelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, IndependenceBoundPlain.PlainCoefficientIdentity X H

theorem independence_bound_self_conj (h : CoefficientIdentitySelfConjugate) : IndependenceBoundSelfConjugate := by
  unfold IndependenceBoundSelfConjugate AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.rawSelf p) hrk H hR2 (h C V O dd Y d I0 p hrk H)

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.LeafHolds
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section EqOn

variable {K : Type} [Field K] {σ : Type}

def EqOn (A : Set σ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, (↑μ.support : Set σ) ⊆ A → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G

theorem EqOn.refl (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := fun _ _ => rfl

theorem EqOn.mul {A : Set σ} {F G F' G' : MvPowerSeries σ K} (h : EqOn A F G) (h' : EqOn A F' G') :
    EqOn A (F * F') (G * G') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hs : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h1 : (↑p.1.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.1 ≤ μ := hs ▸ le_self_add
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  have h2 : (↑p.2.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.2 ≤ μ := hs ▸ le_add_self
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  rw [h p.1 h1, h' p.2 h2]

theorem EqOn.pow {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (k : ℕ) : EqOn A (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem EqOn.prod {A : Set σ} {ι : Type} (s : Finset ι) {F G : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, EqOn A (F i) (G i)) : EqOn A (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem EqOn.mvExp {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by
  intro μ hμ
  show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem EqOn.jet {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (P : MvPolynomial σ K)
    (hP : ∀ μ ∈ P.support, (↑μ.support : Set σ) ⊆ A) : jetAt0 P F = jetAt0 P G := by
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [h μ (hP μ hμ)]

theorem EqOn.rename {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by
  intro ν hν
  by_cases hr : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hr
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    refine h μ fun x hx => hν ?_
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
    exact Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]

end EqOn

theorem leaf_holds : LeafSt := by
  intro C _ V d _ I _ κ _ X H n Po kind hk gr
  rw [rtj_valOf]
  set A : Set (Fin n × WV I) := {x | ∃ μ ∈ Po.support, μ x ≠ 0} with hA
  refine EqOn.jet (A := A) ?_ Po fun μ hμ x hx => ⟨μ, hμ, Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)⟩
  refine EqOn.prod _ fun ρ _ => (EqOn.refl A _).mul (EqOn.mvExp ?_)
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq]
  refine EqOn.rename (rtjR ρ) fun μ hμ => ?_
  cases hkd : kind ρ with
  | none =>
    obtain ⟨g, hg⟩ := hk.2 ρ hkd
    have h1 : ∀ w ∈ μ.support, w.1 = g := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact hg μ' hμ' w hne
    have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
      fin_cases g
      · exact Or.inl h1
      · exact Or.inr h1
    rw [H.axes μ h2]
    simp [rtjH]
  | some q =>
    obtain ⟨g, a, a'⟩ := q
    have h1 : ∀ w ∈ μ.support, X.OnLf g a a' w := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact (hk.1 ρ g a a' hkd).2.2 μ' hμ' w hne
    show MvPowerSeries.coeff μ X.hRow =
      (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0)
    rw [if_pos h1]

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCuts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def LogExSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (dd : ℕ) (G : FGLaw C dd), ∃ lg ex : Pt C 1 dd,
    (∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)) ∧
    (∀ i, ev (n := 2) ![addOf G.F (pt C dd 0) (pt C dd 1)] (lg i) =
      ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)) ∧
    (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt C dd 0 ∧ comp1 ex lg = pt C dd 0

structure IsMapFB {K C : Type} [Field K] [Field C] (φ : K →+* C) {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (B : FB K dd O) (B' : FB C dd O) : Prop where
  F : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j)
  act : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)
  ph1 : B'.ph1 = MvPowerSeries.map φ B.ph1
  ph2 : B'.ph2 = MvPowerSeries.map φ B.ph2
  sy : B'.sy = MvPowerSeries.map φ B.sy
  ad : ∀ a, B'.ad a = MvPowerSeries.map φ (B.ad a)

def FBMapSt : Prop :=
  ∀ (K C : Type) [Field K] [Field C] (φ : K →+* C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (B : FB K dd O),
    ∃ B' : FB C dd O, IsMapFB φ B B'

def GaugeMapSt : Prop :=
  ∀ (K C : Type) [Field K] [Field C] [CharZero K] [CharZero C] (φ : K →+* C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (B : FB K dd O) (B' : FB C dd O), IsMapFB φ B B' →
    ∀ h : PS K 2 dd, B.IsCanonGauge K h → B'.IsCanonGauge C (MvPowerSeries.map φ h)

def EmbIntSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ t : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr t))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartDerivativeCoefficient (C3 : IntChart T io y) (k n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  nabValN (a3B C3) T.Fr (a3h C3) H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) P

theorem nuLocC_le_nval (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by
  unfold nuLocC chartDerivativeCoefficient
  exact le_trans (iInf₂_le P hP) (iInf₂_le f hf)

end Chart

section Val

variable {C : Type} [Field C] {V : VF C}

theorem le_v_sum (x : WithTop ℝ) {m : ℕ} (z : Fin m → C) (h : ∀ i, x ≤ V.v (z i)) : x ≤ V.v (∑ i, z i) := by
  refine Finset.sum_induction z (fun w => x ≤ V.v w)
    (fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)) ?_ (fun i _ => h i)
  rw [AddValuation.map_zero]
  exact le_top

end Val

variable (Xo c)

def NabMapSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C)
    (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr),
      Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι f) (MvPolynomial.map ι P) = ι (chartDerivativeCoefficient C3 k n f P)

def DescSpanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P ∈ (chartLetterSystem C3 V ι a).FF n, ∀ f : PS C n (chD C3.ch), IntS V f →
      ∃ (m : ℕ) (r : Fin m → C) (Pi : Fin m → MvPolynomial (LtN Dw n) T.Fr) (fi : Fin m → PS T.Fr n (chD C3.ch)),
        (∀ i, V.Ge 0 (r i)) ∧ (∀ i, Pi i ∈ FFV (Dw := Dw) T a n) ∧ (∀ i, IsIntPS T (fi i)) ∧
        Y.nab (chartLetterSystem C3 V ι a) n f P =
          ∑ i, r i * Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i))

def NvalEqSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ x : T.Fr, (WithBot.some (V.v (ι x)) : WithBot (WithTop ℝ)) = nval T.V (eOf T V) x

variable {Xo c}

theorem descent_of (h1 : NabMapSt Xo c) (h2 : DescSpanSt Xo c) (h3 : NvalEqSt) : DescentSt Xo c := by
  intro T io y C3 C _ _ V ι hι k Y hY a n
  unfold FBChart.nuPlE
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨P, hP, f, hf, rfl⟩ := hx
  obtain ⟨m, r, Pi, fi, hr, hPi, hfi, heq⟩ := h2 T io y C3 C V ι hι k Y hY a n P hP f hf
  have hz : ∀ i, nuLocC C3 (eOf T V) k a n ≤ (WithBot.some (V.v (Y.nab (chartLetterSystem C3 V ι a) n
      (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i)))) : WithBot (WithTop ℝ)) := by
    intro i
    rw [h1 T io y C3 C V ι k Y hY a n (fi i) (Pi i), h3 T C V ι hι]
    exact nuLocC_le_nval C3 (eOf T V) k a n (Pi i) (hPi i) (fi i) (hfi i)
  rw [heq]
  generalize nuLocC C3 (eOf T V) k a n = ν at hz ⊢
  rcases ν with _ | w
  · exact bot_le
  · refine WithBot.coe_le_coe.mpr (le_v_sum w _ fun i => ?_)
    have hzi := WithBot.coe_le_coe.mp (hz i)
    rw [AddValuation.map_mul]
    calc w = 0 + w := (zero_add w).symm
      _ ≤ V.v (r i) + _ := add_le_add (hr i) hzi

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem van_sum {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by
  intro ν hν
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi ν hν)

theorem van_X {τ : Type} {T : Set τ} {q : τ} (hq : q ∈ T) : Van T (X q : MvPowerSeries τ C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · exfalso
    exact hν q (by rw [h]; simp) hq
  · rfl

theorem van_univ {τ : Type} {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) : Van Set.univ f := by
  intro ν hν
  have h0 : ν = 0 := by
    ext w
    by_contra h
    exact hν w (Finsupp.mem_support_iff.mpr h) (Set.mem_univ _)
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hf

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) (hf : constantCoeff f = 0) :
    constantCoeff (inCol col f) = 0 := by
  have hb : MvPowerSeries.HasSubst
      (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  unfold inCol
  rw [MvPowerSeries.constantCoeff_subst hb, finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => (MvPowerSeries.X (col, s) : MvPowerSeries (Fin 2 × Fin dd) C) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hi]
    rw [h0, smul_zero]

theorem van_hCol (col g : Fin 2) (h : PS C 2 dd)
    (hh : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    Van {w : Fin 2 × (Fin 2 × Fin dd) | w.1 = g} (hCol col h) := by
  unfold hCol
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = g} (fun _ => constantCoeff_X _) ?_ ?_
  · intro s hs
    exact van_X hs
  · intro e he
    exact hh e he

theorem gauge_axes (Y : FBChart C V O dd) (g : Fin 2) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0 := by
  fin_cases g
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem axesSelf_holds : AxesSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
    apply constantCoeff_inCol
    rw [constantCoeff_uncurry]
    exact Y.ex_const x.2
  · intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    exact van_sum Finset.univ _ (fun col _ => van_hCol col g Y.h (gauge_axes Y g)) e he

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValBlocksChart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (I o) (J o)} {n : ℕ}

theorem valBlocks_fin {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (hM : BlockMembership X n F FFimg Z ga)
    (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : ValBlocks X F Z n ga ν :=
  valBlocks_G hV jetProd F Z ga hM (blkAdm X F Z ga hdich hj hga)

end G

section Cc

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ}

theorem valBlocksC_fin {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (nW : ℕ) (hn : nW ≤ 2 * n + 1) (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate X n F FFimg gaC)
    (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n) (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) :
    ValBlocksC X F nW gaC ν :=
  valBlocksC_G hV jetProd F nW hn gaC hM (blkAdmC X F gaC hA hj hga)

end Cc

section FB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
  (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem valBlocks_chart (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n)
    (hM : BlockMembershipChart Y p H Ls n F Z ga)
    (hdich : ∀ o ∈ Z, (rd Y p H o).Alt ∨ ∀ a, (rd Y p H o).big 0 a) (hj : ∀ o ∈ Z, (rd Y p H o).j' < (rd Y p H o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (rd Y p H o).rkF g a) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_fin (valO_of Y p H Ls n ν (lower_of_nuPlE Y Ls n ν hν) hs hv) F Z ga hM hdich hj hga

end FB

end Formalism.L2.FormalSeriesBounds.RF
end
end

