import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.AdjointCanonicalGauge
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge

abbrev Ints (C : Type) [NormedField C] [IsUltrametricDist C] : Type :=
  (NormedField.valuation (K := C)).integer

def IsOddResChar (C : Type) [NormedField C] (g : ℕ) : Prop :=
  g.Prime ∧ Odd g ∧ ‖(g : C)‖ < 1

def SplitsCompletely (E : Type) [Field E] [NumberField E] (O : Type) [CommRing O] (g : ℕ) : Prop :=
  ((Ideal.span {(g : ℤ)}).primesOver O).ncard = Module.finrank ℚ E

def StarIsConj (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (O : Type) [CommRing O]
    [StarRing O] [Algebra O E] : Prop :=
  ∀ a : O, algebraMap O E (star a) = NumberField.IsCMField.complexConj E (algebraMap O E a)

section Defs

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra R k]

def IntBelow {n : ℕ} (g : ℕ) (f : PS k n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, ∑ p, m p < g → coeff m f ∈ (algebraMap R k).range

def IntBelowBi (g : ℕ) (f : PS k 2 d) : Prop :=
  ∀ m : Fin 2 × Fin d →₀ ℕ, ∑ i, m (0, i) < g → ∑ j, m (1, j) < g → coeff m f ∈ (algebraMap R k).range

def IntBilin (f : PS k 2 d) : Prop :=
  ∀ i j, bilinPart k f i j ∈ (algebraMap R k).range

def IsAdditive (G : FGLaw R d) (ℓ : Pt k 1 d) : Prop :=
  (∀ i, constantCoeff (ℓ i) = 0) ∧
    comp1 ℓ (addOf (G.mapF (algebraMap R k)) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)

def IsLogExp (G : FGLaw R d) (ℓ ex : Pt k 1 d) : Prop :=
  IsAdditive k G ℓ ∧ dLin ℓ = 1 ∧ IsInvPair ℓ ex

def inLetters {n : ℕ} (ex : Pt k 1 d) (f : PS k n d) : PS k n d :=
  ev (n := n) (fun i => comp1 ex (pt k (n := n) d i)) f

variable [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O]

def IsBiaddGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0 ∧
    FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) ∧
    FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)

def IsAdjGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  IsBiaddGauge k B h ∧ ∀ a : O, FB.toK k (B.ad a) =
    FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

def IsFrameFactor (u : PS R 2 d) : Prop :=
  ev (n := 1) ![0, pt R d 0] u = 1 ∧ ev (n := 1) ![pt R d 0, 0] u = 1

def colProd (B : FB R d O) (w0 : O) (n : ℕ) (u : PS R 2 d) : PS R n d :=
  ∏ i : Fin n, ev (n := n) ![pt R d i, comp1 (B.A.act w0) (pt R d i)] u

def colSum (B : FB R d O) (w0 : O) (n : ℕ) (h : PS k 2 d) : PS k n d :=
  ∑ i : Fin n, ev (n := n) ![pt k d i, comp1 (B.actK k w0) (pt k d i)] h

def IsLetters {E : Type} [Field E] [Algebra O E] (B : FB R d O) (t : Fin d → (E →+* k)) (ℓ ex : Pt k 1 d) : Prop :=
  IsAdditive k B.G ℓ ∧ IsInvPair ℓ ex ∧
    (∃ M : GL (Fin d) R, dLin ℓ = (M : Matrix (Fin d) (Fin d) R).map (algebraMap R k)) ∧
    ∀ (a : O) (i : Fin d), comp1 ℓ (B.actK k a) i = C (t i (algebraMap O E a)) * ℓ i

end Defs

def IsConjType {E k : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [CommRing k]
    (τ τ' : E →+* k) : Prop :=
  ∀ x : E, τ' x = τ (NumberField.IsCMField.complexConj E x)

def LogIntegral : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (d : ℕ) (G : FGLaw (Ints C) d),
      (∃ ℓ ex : Pt C 1 d, IsLogExp C G ℓ ex) ∧
      ∀ ℓ ex : Pt C 1 d, IsLogExp C G ℓ ex →
        (∀ i, IntBelow (R := Ints C) C g (ℓ i)) ∧ ∀ i, IntBelow (R := Ints C) C g (ex i)

def GaugeIntegral : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB (Ints C) d O)
      (ℓ ex : Pt C 1 d), IsLogExp C B.G ℓ ex → ∀ h : PS C 2 d, IsBiaddGauge C B h →
      IntBilin (R := Ints C) C (inLetters C ex h) → IntBelowBi (R := Ints C) C g (inLetters C ex h)

def AdjointGauge : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
      (O : Type) [CommRing O] [StarRing O] [Algebra O E] [IsIntegralClosure O ℤ E],
      StarIsConj E O → SplitsCompletely E O g → ∀ (d : ℕ) (B : FB (Ints C) d O),
        ∃ h' : PS C 2 d, IsAdjGauge C B h' ∧ IntBilin (R := Ints C) C h'

def ProductFrame : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
      (O : Type) [CommRing O] [StarRing O] [Algebra O E] [IsIntegralClosure O ℤ E],
      StarIsConj E O → SplitsCompletely E O g → ∀ w0 : O, w0 + star w0 = 1 →
      ∀ (d : ℕ) (B : FB (Ints C) d O),
        (∃ (t : Fin d → (E →+* C)) (ℓ ex : Pt C 1 d), IsLetters C B t ℓ ex) ∧
        ∃ (u : PS (Ints C) 2 d) (h0 : PS C 2 d), IsFrameFactor u ∧ IsAdjGauge C B h0 ∧
          ∀ n : ℕ, ∃ hL : PS C n d, constantCoeff hL = 0 ∧
            FB.toK C (colProd B w0 n u) * FB.expS C (colSum C B w0 n h0) = FB.expS C hL ∧
            ∀ (t : Fin d → (E →+* C)) (ℓ ex : Pt C 1 d), IsLetters C B t ℓ ex →
              IntBelow (R := Ints C) C g (inLetters C ex hL) ∧
              ∀ m : Fin n × Fin d →₀ ℕ, coeff m (inLetters C ex hL) ≠ 0 →
                3 ≤ ∑ p, m p ∧
                ∃ (i : Fin n) (a b : Fin d), (∀ p, m p ≠ 0 → p.1 = i ∧ (t p.2 = t a ∨ t p.2 = t b)) ∧
                  m (i, a) ≠ 0 ∧ m (i, b) ≠ 0 ∧ IsConjType (t a) (t b)

def GaugeBelowResChar : Prop :=
  LogIntegral ∧ GaugeIntegral ∧ AdjointGauge ∧ ProductFrame

example : CompleteSpace ℂ_[3] ∧ IsAlgClosed ℂ_[3] ∧ CharZero ℂ_[3] ∧ IsUltrametricDist ℂ_[3] :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedFrameGauge
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge

section Frames

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

structure IsBalancedGauge (B : FB R d O) (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, FB.toK k (B.ad a) = FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

theorem isBalancedGauge_of_canon (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h) :
    IsBalancedGauge k B h :=
  ⟨hh.ax0, hh.ax1, hh.ph1, hh.ph2, hh.ad⟩

end Frames

section Columns

variable {k : Type} [CommRing k] {d n : ℕ}

def DCol (F : Fin d → PS k 2 d) (u : Fin d → k) (b : Fin n) (f : PS k n d) : PS k n d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := n) ![pt k d b, 0] (pderiv k ((1 : Fin 2), i) (F j))) *
    pderiv k (b, j) f

def DPolyCols (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial (ι × Fin n) k) (f : PS k n d) : PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (DCol F (u p.1) p.2)^[m p] g) f

example (F : Fin d → PS k 2 d) (u : Fin d → k) (f : PS k 1 d) : DCol F u 0 f = Dof F u f := rfl

end Columns

section Value

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def quotCols (B : FB R d O) (h : PS k 2 d) (w0 : O) (N : ℕ) {n : ℕ} (f : PS k n d) : PS k n d :=
  f * ∏ b : Fin n, FB.expS k (ev (n := n) ![pt k d b, comp1 (B.actK k w0) (pt k d b)] h) ^ N

def valCols (B : FB R d O) (h : PS k 2 d) (w0 : O) (N : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) : k :=
  constantCoeff (DPolyCols (B.FK k) u P (quotCols k B h w0 N f))

end Value

section Letters

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def conjType {k : Type} [Field k] (τ : E →+* k) : E →+* k :=
  τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom

variable {E}

def lieEigen {R : Type} [CommRing R] {d : ℕ} [StarRing (𝓞 E)] (k : Type) [Field k] [Algebra R k]
    (B : FB R d (𝓞 E)) (τ : E →+* k) : Submodule k (Fin d → k) where
  carrier := {v | ∀ a : 𝓞 E, (dAct k B a).mulVec v = τ (a : E) • v}
  add_mem' := fun {v w} hv hw a => by
    rw [Matrix.mulVec_add, hv a, hw a, smul_add]
  zero_mem' := fun a => by simp
  smul_mem' := fun c v hv a => by
    rw [Matrix.mulVec_smul, hv a, smul_comm]

def IsHarmonic {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) : Prop :=
  ∀ (τ : E →+* k) (i : Fin (r τ)) (i' : Fin (r (conjType E τ))),
    ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* k, Fin (r τ)), b)
      (MvPolynomial.pderiv ((⟨conjType E τ, i'⟩ : Σ τ : E →+* k, Fin (r τ)), b) P) = 0

example {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ} (c : k) :
    IsHarmonic r (n := n) (MvPolynomial.C c) := by
  intro τ i i'
  simp

example {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ} (p : (Σ τ : E →+* k, Fin (r τ)) × Fin n) :
    IsHarmonic r (n := n) (MvPolynomial.X p) := by
  classical
  intro τ i i'
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

end Letters

def BalancedFrameValue : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (k : Type) [Field k] [CharZero k], Fintype.card (E →+* k) = Module.finrank ℚ E →
  ∀ (R : Type) [CommRing R] [Algebra R k] (d : ℕ) (B : FB R d (𝓞 E)) (w0 : 𝓞 E), w0 + star w0 = 1 →
  ∀ (r : (E →+* k) → ℕ) (u : (Σ τ : E →+* k, Fin (r τ)) → Fin d → k),
    (∀ τ : E →+* k, LinearIndependent k (fun i : Fin (r τ) => u ⟨τ, i⟩) ∧
      Submodule.span k (Set.range fun i : Fin (r τ) => u ⟨τ, i⟩) = lieEigen k B τ) →
  ∀ (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k), IsHarmonic r P →
  ∀ (h h' : PS k 2 d), B.IsCanonGauge k h → IsBalancedGauge k B h' →
  ∀ f : PS k n d, valCols k B h w0 N f u P = valCols k B h' w0 N f u P

section Inhabitant

variable {k : Type} [CommRing k] {g m n : ℕ} {O : Type} [CommRing O]

def addSeries (k : Type) [CommRing k] (g : ℕ) : Fin g → PS k 2 g :=
  fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)

theorem eval_addSeries_two (a : Fin 2 → Pt k n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addSeries k g i) = a 0 i + a 1 i := by
  unfold addSeries ev
  rw [subst_add (hasSubst_of_constantCoeff_zero ha), subst_X (hasSubst_of_constantCoeff_zero ha),
    subst_X (hasSubst_of_constantCoeff_zero ha)]

theorem eval_const_mul_X (a : Fin 1 → Pt k n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : k)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS k 1 g) = C c * a 0 i := by
  unfold ev
  rw [subst_mul (hasSubst_of_constantCoeff_zero ha), subst_X (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  rw [subst_C]

theorem addOf_addSeries (a b : Pt k n g) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : addOf (addSeries k g) a b = a + b := by
  funext i
  exact eval_addSeries_two ![a, b] (fun ⟨j, l⟩ => by fin_cases j; exacts [ha l, hb l]) i

theorem expS_zero [Algebra ℚ k] : FB.expS k (0 : PS k n g) = 1 := by
  ext e
  rw [FB.expS, PowerSeries.coeff_subst PowerSeries.HasSubst.zero, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    simp [zero_pow hj]

theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt k g j i) = 0 := by simp [pt]

def addLaw (k : Type) [CommRing k] (g : ℕ) : FGLaw k g where
  F := addSeries k g
  const i := by simp [addSeries]
  unit i := by
    rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addSeries, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt k g 0, pt k g 1] (addSeries k g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS k 3 g) :=
      funext fun l => by rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt k g 1, pt k g 2] (addSeries k g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS k 3 g) :=
      funext fun l => by rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt]),
      eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]

def diagSeries (χ : Fin g → (O →+* k)) (a : O) : Pt k 1 g := fun l => C (χ l a) * X ((0 : Fin 1), l)

theorem cc_diag (χ : Fin g → (O →+* k)) (a : O) (i : Fin g) : constantCoeff (diagSeries χ a i) = 0 := by
  simp [diagSeries]

theorem comp_diagonalSeries (χ : Fin g → (O →+* k)) (a : O) (b : Pt k n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (diagSeries χ a) b = fun i => C (χ i a) * b i := by
  funext i
  exact eval_const_mul_X ![b] (fun ⟨j, l⟩ => by fin_cases j; exact hb l) _ i

def diagAct (χ : Fin g → (O →+* k)) : OAct O (addLaw k g) where
  act := diagSeries χ
  const := cc_diag χ
  hom a := by
    show comp1 (diagSeries χ a) (addOf (addSeries k g) (pt k g 0) (pt k g 1)) =
      addOf (addSeries k g) (comp1 (diagSeries χ a) (pt k g 0)) (comp1 (diagSeries χ a) (pt k g 1))
    rw [addOf_addSeries _ _ (cc_pt 0) (cc_pt 1), comp_diagonalSeries _ _ _ (fun i => by simp [pt]),
      comp_diagonalSeries _ _ _ (cc_pt 0), comp_diagonalSeries _ _ _ (cc_pt 1), addOf_addSeries _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show diagSeries χ (a + b) = addOf (addSeries k g) (diagSeries χ a) (diagSeries χ b)
    rw [addOf_addSeries _ _ (cc_diag χ a) (cc_diag χ b)]
    funext i
    simp [diagSeries, add_mul]
  mul_act a b := by
    show diagSeries χ (a * b) = comp1 (diagSeries χ a) (diagSeries χ b)
    rw [comp_diagonalSeries _ _ _ (cc_diag χ b)]
    funext i
    simp [diagSeries, mul_assoc]
  one_act := by
    funext i
    simp [diagSeries, pt]

end Inhabitant

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge
end
end

