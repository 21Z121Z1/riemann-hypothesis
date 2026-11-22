import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.PositiveSignKForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveSignKForm

open GlobalTheory.CM

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def kForm (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

def IsPosSign (D : Datum H) (ε : ℤˣ) : Prop := ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x

theorem IsPosSign.unique {D : Datum H} [Nontrivial D.La] {ε ε' : ℤˣ} (h : IsPosSign D ε) (h' : IsPosSign D ε') :
    ε = ε' := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have h₁ := h x hx
  have h₂ := h' x hx
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    first | rfl | (simp at h₁ h₂; omega)

end Form

def TensorObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H), 1 ≤ D.p + D.q →
  ∀ (M : Type) [Field M] [NumberField M] (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ),
    (D.q = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = H.rt0) ∨ (D.p = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = -H.rt0) →
    C.IsPrincipalAt (σ.comp (algebraMap (𝓞 M) M)) →
    ∃ (ε : ℤˣ) (T : PAT H (Sp (𝓞 M))), IsPosSign D ε ∧ Nonempty (IsTen C D (kForm D ε) T) ∧
      ∃ (K₁ : IntermediateField ℚ ℂ) (hK : KA l ≤ K₁) (jM : M →+* K₁)
        (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom)),
        FiniteDimensional ℚ K₁ ∧ (algebraMap K₁ ℂ).comp jM = σ ∧
        Nonempty (SABMap o.t T.t (spMap (jM.comp (algebraMap (𝓞 M) M))))

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TiedToLattices {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) {K₁ : Type} [Field K₁] [NumberField K₁] {ρ : 𝓞 K₁} {σ₁ : K₁ →+* ℂ}
    (X : CMObj H K₁ ρ σ₁ p q)
    (eB : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)) : Prop :=
  X.hh = Z.hh ∧ IsExp X.B (σ₁.comp (algebraMap (𝓞 K₁) K₁)) D ty Pe eB ∧
  ∃ (g₁ : Bool → ℕ) (ty₁ : ∀ b, Fin (g₁ b) → (E →+* ℂ)) (Pe₁ : ∀ b, (Z.D₁ b).La →+ (Fin (g₁ b) → ℂ))
    (e₁ : ∀ b, (Fin (g₁ b) → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G)),
    (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (ty₁ b) ∧
      IsExp (X.A b) (σ₁.comp (algebraMap (𝓞 K₁) K₁)) (Z.D₁ b) (ty₁ b) (Pe₁ b) (e₁ b)) ∧
    ∀ j : Fin p ⊕ Fin q, ∃ F : (Fin (g₁ j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ a, F (Pe₁ j.isLeft a) = Pe (Z.f j a)) ∧ ∀ z, e₁ j.isLeft z ≫ X.φ j = eB (F z)

end Comparison₂

def CMObject : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l),
    1 ≤ D.p + D.q →
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
  ∀ (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q) (K' : IntermediateField ℚ ℂ), FiniteDimensional ℚ K' →
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hK : KA l ≤ K₁) (ρ : 𝓞 K₁)
      (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t : SAB H (Sp K₁))
      (m : SABMap t Xo.univ.t y) (n : SABMap t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
      (eB : (Fin g → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
      K' ≤ K₁ ∧ algebraMap K₁ ℂ (ρ : K₁) = H.rt0 ∧
      y ≫ Xo.s = spMap (IntermediateField.inclusion hK).toRingHom ∧
      spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
      (∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left) ∧
      TiedToLattices Z X eB

def Existence : Prop := TensorObject ∧ CMObject

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveSignKForm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition

section Series
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
  {N : NumD C}

def ThetaSum (ν : NumOf D C N) (m : ℕ) (p : QkPt D C (m ^ 2)) (v : C) : Prop :=
  ∃ q : N.QT (m ^ 2), ν.QPt p q ∧ HasSum (N.txT m q) v

def CoordSum (ν : NumOf D C N) (m : ℕ) (p : QkPt D C (m ^ 2)) (h : GtPtF D C) (v : C) : Prop :=
  ∃ (q : N.QT (m ^ 2)) (hv : N.Gt), ν.QPt p q ∧ ν.Pt h hv ∧ HasSum (N.evT m q hv) v

theorem qPt_unique (ν : NumOf D C N) {k : ℕ} {p : QkPt D C k} {q q' : N.QT k} (h : ν.QPt p q) (h' : ν.QPt p q') :
    q = q' :=
  Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (ν.eX.injective (h.1.trans h'.1.symm))) (ν.pt_unique h.2 h'.2))

theorem ThetaSum.hasSum {ν : NumOf D C N} {m : ℕ} {p : QkPt D C (m ^ 2)} {v : C} (h : ThetaSum ν m p v)
    {q : N.QT (m ^ 2)} (hq : ν.QPt p q) : Summable (N.txT m q) ∧ N.tx m q = v := by
  obtain ⟨q', h₁, h₂⟩ := h
  obtain rfl := qPt_unique ν h₁ hq
  exact ⟨h₂.summable, h₂.tsum_eq⟩
end Series

def SeriesAt {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : Unif I D A G) {C : Type} [NormedField C] [Algebra (FractionRing V) C] {N : NumD C} (ν : NumOf D.toPre C N)
    (m : ℕ) : Prop :=
  ∀ (Ix : Type) (p : Ix → QkPt D.toPre C (m ^ 2)) (x : Ix → (TFK (R := V) C ⟶ A.A)),
    (∀ i, QkToAkU U.toUnifPre C (m ^ 2) (p i) (x i)) →
    (∃ v : Ix → C, (∀ i, ThetaSum ν m (p i) (v i)) ∧ IsThetaPt A m (T := TFK (R := V) C) x fun i => fnOf (v i)) ∧
    ∀ (j : ℕ), 0 < j → ∀ (r : QkPt D.toPre C j) (z : TFK (R := V) C ⟶ A.A), QkToAkU U.toUnifPre C j r z →
      ∃ v : Ix → C, (∀ i, CoordSum ν m (p i) r.g (v i)) ∧ IsCoordPt A m (T := TFK (R := V) C) x z fun i => fnOf (v i)

def SeriesFor (lev : ∀ (V : Type) [CommRing V], ℕ → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
  ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G)
    (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing V) C],
    CExt V (IsLocalRing.maximalIdeal V) C →
  ∀ (N : NumD C) (ν : NumOf D.toPre C N) (m : ℕ), lev V m → SeriesAt U ν m

def ThetaSeriesSt : Prop := SeriesFor fun _ _ m => Odd m

def ThetaSeriesPrimeSt : Prop :=
  SeriesFor fun V _ m => ∃ n k : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : V) ∧ m = n ^ k

theorem ThetaSeriesSt.prime (h : ThetaSeriesSt) : ThetaSeriesPrimeSt := by
  rintro V _ _ _ hV D A G _ _ U C _ _ _ _ _ hC N ν m ⟨n, k, -, hn, -, rfl⟩
  exact h V hV D A G U C hC N ν _ hn.pow

structure TowerIso {C : Type} [Field C] (N N' : NumD C) (n : ℕ) where

  io : ∀ j : ℕ, N.QT ((n ^ j) ^ 2) → N'.QT ((n ^ j) ^ 2)

  eqv : ∀ j p q, N'.QEq (io j p) (io j q) ↔ N.QEq p q

  onto : ∀ j p', ∃ p, N'.QEq (io j p) p'

  mul : ∀ j p q, N'.QEq (io j (p * q)) (io j p * io j q)

  incl : ∀ j (p : N.QT ((n ^ j) ^ 2)) (q : N.QT ((n ^ (j + 1)) ^ 2)) (q' : N'.QT ((n ^ (j + 1)) ^ 2)),
    q.1.1.toAdd = n ^ 2 • p.1.1.toAdd → q.1.2 = p.1.2 →
    q'.1.1.toAdd = n ^ 2 • (io j p).1.1.toAdd → q'.1.2 = (io j p).1.2 → N'.QEq (io (j + 1) q) q'

  wp : ∀ j p q, N'.wp (io j p) (io j q) = N.wp p q

def TowerIso.Proportional {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (w : TowerIso N N' n) (c₀ : C) : Prop :=
  ∀ j p, ∃ v, HasSum (N.txT (n ^ j) p) v ∧ HasSum (N'.txT (n ^ j) (w.io j p)) (c₀ * v)

section Rec
variable {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [Field C] [Algebra (FractionRing V) C]
  {N N' : NumD C}

def TowerIso.RationalAt {n : ℕ} (w : TowerIso N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N') (j : ℕ) : Prop :=
  ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C ((n ^ j) ^ 2)) (p' pσ' : QkPt D' C ((n ^ j) ^ 2))
    (q qσ : N.QT ((n ^ j) ^ 2)) (q' qσ' : N'.QT ((n ^ j) ^ 2)),
    QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ → ν'.QPt p' q' → ν'.QPt pσ' qσ' →
    N'.QEq (w.io j q) q' → N'.QEq (w.io j qσ) qσ'

def Carries (e : IsPullDeg (RingHom.id V) D D') {k : ℕ} (p : QkPt D C k) (p' : QkPt D' C k) : Prop :=
  e.xe p'.y = p.y ∧ ∀ χ : D'.X, GenRel (F := C) e.w (p'.g.s χ) (p.g.s (e.xe χ)) 1

def TowerIso.InducedBy {n : ℕ} (w : TowerIso N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N')
    (e : IsPullDeg (RingHom.id V) D D') : Prop :=
  ∀ j (q : N.QT ((n ^ j) ^ 2)), ∃ (p : QkPt D C ((n ^ j) ^ 2)) (p' : QkPt D' C ((n ^ j) ^ 2)) (q' : N'.QT ((n ^ j) ^ 2)),
    ν.QPt p q ∧ ν'.QPt p' q' ∧ Carries e p p' ∧ N'.QEq (w.io j q) q'
end Rec

def RecognitionSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
  ∀ (D D' : DegData V (IsLocalRing.maximalIdeal V)) (n : ℕ), n.Prime → Odd n → IsUnit (n : V) →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing V) C],
    CExt V (IsLocalRing.maximalIdeal V) C →
  ∀ (N N' : NumD C) (ν : NumOf D.toPre C N) (ν' : NumOf D'.toPre C N') (w : TowerIso N N' n) (c₀ : C),
    w.Proportional c₀ → (∃ j, 1 ≤ j ∧ w.RationalAt ν ν' j) →
    ∃ e : IsPullDeg (RingHom.id V) D.toPre D'.toPre, w.InducedBy ν ν' e

def SeriesAndRecognition : Prop := ThetaSeriesSt ∧ RecognitionSt

def TowerIso.refl {C : Type} [Field C] (N : NumD C) (n : ℕ) : TowerIso N N n where
  io _ p := p
  eqv _ _ _ := Iff.rfl
  onto _ p := ⟨p, (N.qEq_equivalence _).refl p⟩
  mul _ _ _ := (N.qEq_equivalence _).refl _
  incl _ _ q q' a b c d := by
    have : q = q' := Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (a.trans c.symm)) (b.trans d.symm))
    exact this ▸ (N.qEq_equivalence _).refl _
  wp _ _ _ := rfl

open TateInh in

def tateNeg {C : Type} [Field C] (q : Cˣ) (n : ℕ) : TowerIso (tate q) (tate q) n where
  io _ p := p⁻¹
  eqv _ p r := by
    simp only [NumD.qEq_iff]
    constructor
    · rintro ⟨z, h⟩
      refine ⟨-z, ?_⟩
      have h' := congrArg (·⁻¹) h
      simp only [inv_inv, mul_inv] at h'
      rw [h']
      congr 1
      exact Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, NumD.io_neg]))
    · rintro ⟨z, h⟩
      refine ⟨-z, ?_⟩
      rw [h, mul_inv]
      congr 1
      exact Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, NumD.io_neg]))
  onto _ p := ⟨p⁻¹, by rw [inv_inv]; exact (NumD.qEq_equivalence _ _).refl p⟩
  mul _ _ _ := by rw [mul_inv]; exact (NumD.qEq_equivalence _ _).refl _
  incl _ p r r' a b c d := by
    have : r⁻¹ = r' := Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (by
      rw [c]; change -r.1.1.toAdd = _ • -p.1.1.toAdd; rw [a, smul_neg])) (by
      rw [d]; change r.1.2⁻¹ = p.1.2⁻¹; rw [b]))
    exact this ▸ (NumD.qEq_equivalence _ _).refl _
  wp _ p r := by
    have e : ∀ (g : (tate q).Gt) (a : ℤ), sv g⁻¹ (-a) = sv g a := fun g a => by
      have h := sv_add g a (-a)
      rw [add_neg_cancel, show sv g 0 = 1 from g.s_zero] at h
      change 1 / sv g (-a) = _
      rw [h, mul_div_cancel_right]
    rw [tate_wp_eq, tate_wp_eq]
    exact congrArg₂ (· / ·) (e _ _) (e _ _)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
end
end

