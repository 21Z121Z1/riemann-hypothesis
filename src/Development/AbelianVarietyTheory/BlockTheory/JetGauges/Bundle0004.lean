import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.BiadditiveBalancedSeries
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.BiadditiveBalancedSeries

section Frames

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

structure IsBiaddBalanced (g : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] g = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] g = 0
  add1 : FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] g +
    ev (n := 3) ![pt k d 1, pt k d 2] g -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] g)
  add2 : FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] g +
    ev (n := 3) ![pt k d 0, pt k d 2] g -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] g)
  bal : ∀ a : O, FB.toK k (B.ad a) =
    FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] g -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] g)

theorem IsBiaddBalanced.of_canon {g : PS k 2 d} (h : B.IsCanonGauge k g) : IsBiaddBalanced B k g :=
  ⟨h.ax0, h.ax1, h.ph1, h.ph2, h.ad⟩

end Frames

section Inhabitant

variable {O : Type} [CommRing O] [StarRing O] {k : Type} [Field k] [CharZero k] {d n : ℕ}

omit [CharZero k] in
theorem cc_pt (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by simp [pt]

omit [CharZero k] in
theorem addOf_addLaw (a b : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : addOf (addLaw k d).F a b = a + b := by
  have h : ∀ (l : Fin 2) (m : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt k n d) l m) = 0 := by
    intro l m; fin_cases l; exacts [ha m, hb m]
  funext i
  show ev ![a, b] (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : PS k 2 d) = _
  rw [ev_add _ h, ev_X _ h, ev_X _ h]
  rfl

omit [CharZero k] in
theorem ev_XX (a b : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (i j : Fin d) :
    ev ![a, b] (X ((0 : Fin 2), i) * X ((1 : Fin 2), j) : PS k 2 d) = a i * b j := by
  have h : ∀ (l : Fin 2) (m : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt k n d) l m) = 0 := by
    intro l m; fin_cases l; exacts [ha m, hb m]
  rw [ev_mul _ h, ev_X _ h, ev_X _ h]
  rfl

def diagAct (ty : Fin d → (O →+* k)) (a : O) : Pt k 1 d := fun i => C (ty i a) * X ((0 : Fin 1), i)

omit [CharZero k] [StarRing O] in
theorem comp_diagonalAction (ty : Fin d → (O →+* k)) (a : O) (b : Pt k n d)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (diagAct ty a) b = fun i => C (ty i a) * b i := by
  have h : ∀ (l : Fin 1) (m : Fin d), constantCoeff ((![b] : Fin 1 → Pt k n d) l m) = 0 := by
    intro l m; fin_cases l; exact hb m
  funext i
  show ev ![b] (C (ty i a) * X ((0 : Fin 1), i) : PS k 1 d) = _
  rw [ev_mul _ h, ev_C, ev_X _ h]
  rfl

def diagOAct (ty : Fin d → (O →+* k)) : OAct O (addLaw k d) where
  act := diagAct ty
  const a i := by simp [diagAct]
  hom a := by
    show comp1 (diagAct ty a) (addOf (addLaw k d).F (pt k d 0) (pt k d 1)) =
      addOf (addLaw k d).F (comp1 (diagAct ty a) (pt k d 0)) (comp1 (diagAct ty a) (pt k d 1))
    rw [addOf_addLaw _ _ (cc_pt 0) (cc_pt 1), comp_diagonalAction _ _ _ (fun i => by simp [pt]),
      comp_diagonalAction _ _ _ (cc_pt 0), comp_diagonalAction _ _ _ (cc_pt 1),
      addOf_addLaw _ _ (fun i => by simp [pt]) (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show diagAct ty (a + b) = addOf (addLaw k d).F (diagAct ty a) (diagAct ty b)
    rw [addOf_addLaw _ _ (fun i => by simp [diagAct]) (fun i => by simp [diagAct])]
    funext i
    simp [diagAct, add_mul]
  mul_act a b := by
    rw [comp_diagonalAction _ _ _ (fun i => by simp [diagAct])]
    funext i
    simp [diagAct, mul_assoc]
  one_act := by
    funext i
    simp [diagAct, pt]

theorem expS_zero : FB.expS k (0 : PS k n d) = 1 := by
  ext e
  rw [FB.expS, PowerSeries.coeff_subst PowerSeries.HasSubst.zero, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    simp [zero_pow hj]

theorem isBiaddBalanced_XX (ty : Fin d → (O →+* k)) (i j : Fin d)
    (hij : ∀ a, ty i a = ty j (star a)) :
    IsBiaddBalanced (FB.triv (addLaw k d) (diagOAct ty)) k
      (X ((0 : Fin 2), i) * X ((1 : Fin 2), j)) := by
  have hF : (FB.triv (addLaw k d) (diagOAct ty)).FK k = (addLaw k d).F := by
    funext l
    simp [FB.FK, FGLaw.mapF, FB.triv]
  have hA : ∀ a, (FB.triv (addLaw k d) (diagOAct ty)).actK k a = diagAct ty a := by
    intro a
    funext l
    simp [FB.actK, FB.triv, diagOAct]
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [ev_XX _ _ (by simp) (cc_pt 0)]; simp
  · rw [ev_XX _ _ (cc_pt 0) (by simp)]; simp
  · rw [hF, addOf_addLaw _ _ (cc_pt 0) (cc_pt 1), ev_XX _ _ (cc_pt 0) (cc_pt 2),
      ev_XX _ _ (cc_pt 1) (cc_pt 2), ev_XX _ _ (fun l => by simp [pt]) (cc_pt 2), Pi.add_apply,
      add_mul, sub_self, expS_zero]
    simp [FB.triv]
  · rw [hF, addOf_addLaw _ _ (cc_pt 1) (cc_pt 2), ev_XX _ _ (cc_pt 0) (cc_pt 1),
      ev_XX _ _ (cc_pt 0) (cc_pt 2), ev_XX _ _ (cc_pt 0) (fun l => by simp [pt]), Pi.add_apply,
      mul_add, sub_self, expS_zero]
    simp [FB.triv]
  · rw [hA, hA, comp_diagonalAction _ _ _ (cc_pt 0), comp_diagonalAction _ _ _ (cc_pt 1),
      ev_XX _ _ (fun l => by simp [pt]) (cc_pt 1), ev_XX _ _ (cc_pt 0) (fun l => by simp [pt]),
      hij a, mul_left_comm, mul_assoc, sub_self, expS_zero]
    simp [FB.triv]

omit [CharZero k] in

theorem XX_not_symm (i j : Fin d) (hij : i ≠ j) :
    ev (n := 2) ![pt k d 1, pt k d 0] (X ((0 : Fin 2), i) * X ((1 : Fin 2), j) : PS k 2 d) ≠
      X ((0 : Fin 2), i) * X ((1 : Fin 2), j) := by
  classical
  rw [ev_XX _ _ (cc_pt 1) (cc_pt 0)]
  intro h
  simp only [pt, X_def, monomial_mul_monomial, mul_one] at h
  have h2 := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) h
  rw [coeff_monomial_same, coeff_monomial_ne] at h2
  · exact zero_ne_one h2
  · intro h3
    have h4 := DFunLike.congr_fun h3 ((0 : Fin 2), i)
    simp [hij.symm] at h4

end Inhabitant

section Columns

variable {k : Type} [CommRing k] {d n : ℕ}

def Dcol (F : Fin d → PS k 2 d) (u : Fin d → k) (b : Fin n) (f : PS k n d) : PS k n d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) *
      ev (n := n) ![pt k d b, 0] (pderiv k ((1 : Fin 2), i) (F j))) * pderiv k (b, j) f

def DpolyCol (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial (ι × Fin n) k) (f : PS k n d) : PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr
      (fun p g => (Dcol F (u p.1) p.2)^[m p] g) f

end Columns

section Value

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def colSum (g : PS k 2 d) (w0 : O) (n : ℕ) : PS k n d :=
  ∑ b : Fin n, ev (n := n) ![pt k d b, comp1 (B.actK k w0) (pt k d b)] g

def frameVal (g : PS k 2 d) (w0 : O) (N : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) : k :=
  constantCoeff (DpolyCol (B.FK k) u P (f * FB.expS k ((N : k) • colSum B k g w0 n)))

end Value

section Types

variable {E : Type} [Field E] [NumberField E]
variable {k : Type} [Field k]

def conjEmb [IsCMField E] (τ : E →+* k) : E →+* k :=
  τ.comp (IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E).toRingEquiv.toRingHom

def lieEig [StarRing (𝓞 E)] {R : Type} [CommRing R] [Algebra R k] {d : ℕ}
    (B : FB R d (𝓞 E)) (τ : E →+* k) : Submodule k (Fin d → k) where
  carrier := {v | ∀ a : 𝓞 E, (dAct k B a).mulVec v = τ (a : E) • v}
  add_mem' := by
    intro v w hv hw a
    rw [Matrix.mulVec_add, hv a, hw a, smul_add]
  zero_mem' := by
    intro a
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro c v hv a
    rw [Matrix.mulVec_smul, hv a, smul_comm]

def IsHarmonic [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) : Prop :=
  ∀ (τ : E →+* k) (i : Fin (r τ)) (i' : Fin (r (conjEmb τ))),
    ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* k, Fin (r τ)), b)
      (MvPolynomial.pderiv ((⟨conjEmb τ, i'⟩ : Σ τ : E →+* k, Fin (r τ)), b) P) = 0

theorem isHarmonic_X [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (p : (Σ τ : E →+* k, Fin (r τ)) × Fin n) :
    IsHarmonic r (MvPolynomial.X p : MvPolynomial _ k) := by
  classical
  intro τ i i'
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

end Types

def BiaddBalancedValue : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
    ∀ (k : Type) [Field k] [CharZero k],
    Nat.card (E →+* k) = Module.finrank ℚ E →
    ∀ (R : Type) [CommRing R] [Algebra R k] (d : ℕ) (B : FB R d (𝓞 E))
      (w0 : 𝓞 E), w0 + star w0 = 1 →
    ∀ (r : (E →+* k) → ℕ) (u : ∀ τ : E →+* k, Module.Basis (Fin (r τ)) k (lieEig B τ))
      (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k),
    IsHarmonic r P →
    ∀ (f : PS k n d) (hc g : PS k 2 d), B.IsCanonGauge k hc → IsBiaddBalanced B k g →
      frameVal B k g w0 N f (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P =
        frameVal B k hc w0 N f (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P

end GlobalTheory.IndefiniteRowSideFullHecke.BiadditiveBalancedSeries
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.LogExpAdaptedGauge
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge

abbrev Ints (C : Type) [NormedField C] [IsUltrametricDist C] : Subring C :=
  (NormedField.valuation (K := C)).integer

def SplitsCompletely (g : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E

def conjType {E : Type} [Field E] [NumberField E] [IsCMField E] {C : Type} [Field C]
    (τ : E →+* C) : E →+* C :=
  τ.comp (IsCMField.complexConj E : E →+* E)

def degAt {n d : ℕ} (m : Fin n × Fin d →₀ ℕ) (j : Fin n) : ℕ := ∑ i : Fin d, m (j, i)

def degTot {n d : ℕ} (m : Fin n × Fin d →₀ ℕ) : ℕ := ∑ p : Fin n × Fin d, m p

section Chart

variable {k : Type} [CommRing k] {d : ℕ}

def inChart {n : ℕ} (φ : Pt k 1 d) (f : PS k n d) : PS k n d :=
  ev (fun j : Fin n => comp1 φ (pt k (n := n) d j)) f

def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)

end Chart

section Gauges

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def IsLogExp (G : FGLaw R d) (ℓ ε : Pt k 1 d) : Prop :=
  dLin ℓ = 1 ∧
  comp1 ℓ (addOf (G.mapF (algebraMap R k)) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
    comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) ∧
  IsInvPair ℓ ε

variable {O : Type} [CommRing O] [StarRing O]

def IsBiaddGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0 ∧
  FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) ∧
  FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)

def IsAdjGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  IsBiaddGauge k B h ∧
  ∀ a : O, FB.toK k (B.ad a) =
    FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

def colSum (B : FB R d O) (h : PS k 2 d) (w0 : O) (n : ℕ) : PS k n d :=
  ∑ i : Fin n, ev (n := n) ![pt k d i] (B.hL k h w0)

def colProd (B : FB R d O) (u : PS R 2 d) (w0 : O) (n : ℕ) : PS R n d :=
  ∏ i : Fin n, ev (n := n) ![pt R d i, comp1 (B.A.act w0) (pt R d i)] u

end Gauges

section Integrality

variable {C : Type} [NormedField C] {d : ℕ}

def IntBelow (g : ℕ) {n : ℕ} (f : PS C n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, degTot m < g → ‖coeff m f‖ ≤ 1

def IntBiBelow (g : ℕ) (f : PS C 2 d) : Prop :=
  ∀ m : Fin 2 × Fin d →₀ ℕ, degAt m 0 < g → degAt m 1 < g → ‖coeff m f‖ ≤ 1

def IntBilin (f : PS C 2 d) : Prop :=
  ∀ i j : Fin d, ‖bilinPart C f i j‖ ≤ 1

end Integrality

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

def IsAdapted (B : FB (Ints C) d (𝓞 E)) (U : Matrix (Fin d) (Fin d) (Ints C))
    (ty : Fin d → (E →+* C)) : Prop :=
  IsUnit U ∧ ∀ a : 𝓞 E,
    dAct C B a * U.map (algebraMap (Ints C) C) =
      U.map (algebraMap (Ints C) C) * Matrix.diagonal fun j => ty j (a : E)

def letterChart (ε : Pt C 1 d) (U : Matrix (Fin d) (Fin d) (Ints C)) : Pt C 1 d :=
  comp1 ε (linMap (U.map (algebraMap (Ints C) C)))

def ProductFrameFor (g : ℕ) (B : FB (Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) : Prop :=
  ∃ (u : PS (Ints C) 2 d) (h₂ : PS C 2 d),
    ev (n := 1) ![0, pt (Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (Ints C) d 0, 0] u = 1 ∧
    ev (n := 1) ![0, pt C d 0] h₂ = 0 ∧ ev (n := 1) ![pt C d 0, 0] h₂ = 0 ∧
    FB.toK C u * FB.expS C h = FB.expS C h₂ ∧
    (∀ (U : Matrix (Fin d) (Fin d) (Ints C)) (ty : Fin d → (E →+* C)), IsAdapted B U ty →
      bilinPart C (inChart (letterChart ε U) h₂) = 0 ∧
      ∀ m : Fin 2 × Fin d →₀ ℕ, coeff m (inChart (letterChart ε U) h₂) ≠ 0 →
        ∃ τ : E →+* C, (∀ i, m (0, i) ≠ 0 → ty i = τ) ∧ (∀ j, m (1, j) ≠ 0 → ty j = conjType τ)) ∧
    ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ∀ n : ℕ,
      IsUnit (colProd B u w0 n) ∧
      FB.toK C (colProd B u w0 n) * FB.expS C (colSum C B h w0 n) = FB.expS C (colSum C B h₂ w0 n) ∧
      ∀ (U : Matrix (Fin d) (Fin d) (Ints C)) (ty : Fin d → (E →+* C)), IsAdapted B U ty →
        IntBelow g (inChart (letterChart ε U) (colSum C B h₂ w0 n)) ∧
        ∀ m : Fin n × Fin d →₀ ℕ, coeff m (inChart (letterChart ε U) (colSum C B h₂ w0 n)) ≠ 0 →
          3 ≤ degTot m ∧
          ∃ p q : Fin n × Fin d, m p ≠ 0 ∧ m q ≠ 0 ∧ ty q.2 = conjType (ty p.2)

end Letters

def LogInt : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 → ∀ (d : ℕ) (G : FGLaw (Ints C) d),
      (∃ ℓ ε : Pt C 1 d, IsLogExp C G ℓ ε) ∧
      ∀ ℓ ε : Pt C 1 d, IsLogExp C G ℓ ε → (∀ i, IntBelow g (ℓ i)) ∧ ∀ i, IntBelow g (ε i)

def GaugeInt : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (O : Type) [CommRing O] [StarRing O] (d : ℕ) (B : FB (Ints C) d O) (ℓ ε : Pt C 1 d),
    IsLogExp C B.G ℓ ε → ∀ h : PS C 2 d, IsBiaddGauge C B h →
      IntBilin (inChart ε h) → IntBiBelow g (inChart ε h)

def Adjoint : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h' : PS C 2 d, IsAdjGauge C B h' ∧ IntBilin (inChart ε h')

def ProductFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h : PS C 2 d, IsAdjGauge C B h ∧ ProductFrameFor g B ε h

def Statement : Prop := LogInt ∧ GaugeInt ∧ Adjoint ∧ ProductFrame

def AdjointSym : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h' : PS C 2 d, B.IsCanonGauge C h' ∧ IntBilin (inChart ε h')

def ProductFrameSym : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h : PS C 2 d, B.IsCanonGauge C h ∧ ProductFrameFor g B ε h

example (p : ℕ) [Fact p.Prime] : CompleteSpace ℂ_[p] ∧ IsAlgClosed ℂ_[p] ∧ CharZero ℂ_[p] ∧
    IsUltrametricDist ℂ_[p] :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
end
end

