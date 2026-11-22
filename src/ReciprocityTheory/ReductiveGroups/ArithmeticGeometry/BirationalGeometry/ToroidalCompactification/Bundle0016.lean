import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsAwayNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem units_alg {G : Type} [CommGroup G] {g1 g2 g3 g4 g5 W1 W2 d1 d2 u l0 lI l2 : G} (T1 : W1 = g1 * d1)
    (T2 : W2 = g3 * d2) (E : W1 = W2) (U1 : d1 * u = g2 * l0) (U2 : d2 * u = g4 * l2) (A : g5 = l2 * lI)
    (I : l0 * lI = 1) : g1 * g2 = g3 * g4 * g5 := by
  subst T1 T2 A
  obtain rfl : lI = l0⁻¹ := eq_inv_of_mul_eq_one_right I
  obtain rfl : g2 = d1 * u * l0⁻¹ := eq_mul_inv_of_mul_eq U1.symm
  obtain rfl : g4 = d2 * u * l2⁻¹ := eq_mul_inv_of_mul_eq U2.symm
  obtain rfl : g1 = g3 * d2 * d1⁻¹ := eq_mul_inv_of_mul_eq E
  group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfTrivial
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

def RigidIn {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) {t : SAB H (Sp (PowerSeries k))}
    (P : PELUnif (Ideal.span {PowerSeries.X}) t) (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X) : Prop :=
  WitData a P.D P.oD φ₁ he₁ w₁ e₁ ∧ WitData a P.D P.oD φ₂ he₂ w₂ e₂ ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ (n : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing k) n),
        ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
          (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
        ∀ (q₀ : Out.QkPt a.D₀ F n) (q₁ q₂ : Out.QkPt P.D.toPre F n),
          QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
          (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          Out.QkPt.Equiv P.D.toPre F q₁ q₂

def GammaTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ → e₁ = e₂

def ThetaTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ → φ₁ = φ₂

def WTrivSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ he w₁ e → WitData a P oP φ he w₂ e → w₁ = w₂

def GammaBetaSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    ∀ y z, a.be (e₂.symm (e₁ y)) (e₂.symm (e₁ z)) = a.be y z

def GammaModMSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ →
    ∀ y, ∃ z, e₂.symm (e₁ y) = y + (l.M : ℤ) • z

theorem dataRigid_torsion_of_trivial (hΓ : GammaTrivSt) (hΘ : ThetaTrivSt) (hW : WTrivSt) : DataRigidTorsion := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hw₁ hw₂ hq
  have hR : RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ := And.intro hw₁ (And.intro hw₂ hq)

  have he : e₁ = e₂ := hΓ E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR
  subst he

  have hφ : φ₁ = φ₂ := hΘ E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  subst hφ

  exact ⟨rfl, rfl, heq_of_eq (hW E H D l c k bF a P.D P.oD φ₁ he₁ w₁ w₂ e₁ hw₁ hw₂)⟩

theorem gammaTriv (hBe : GammaBetaSt) (hMo : GammaModMSt) (hF : LatFinOrdSt) (hK : LatMinkowskiSt) : GammaTrivSt := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR
  have hR0 := hR
  obtain ⟨hw₁, hw₂, -⟩ := hR0
  have hβ := hBe E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hw₁ hw₂
  have hM := hMo E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hR

  let σ : a.D₀.X ≃ₗ[ℤ] a.D₀.X := (e₁.trans e₂.symm).toAddEquiv.toIntLinearEquiv
  have hσapp : ∀ y, σ y = e₂.symm (e₁ y) := fun y => rfl
  obtain ⟨n, hn, hσn⟩ := hF a.D₀.X a.be a.be_symm a.be_pos σ
    (fun y z => by rw [hσapp, hσapp]; exact hβ y z)
  have hσ : σ = 1 := by
    refine hK a.D₀.X σ n l.M hn hσn l.three_le (fun y => ?_)
    obtain ⟨z, hz⟩ := hM y
    refine ⟨z, ?_⟩
    rw [hσapp, hz]
    simp
  ext y
  have h1 : σ y = y := by rw [hσ]; rfl
  rw [hσapp] at h1
  exact (LinearEquiv.symm_apply_eq e₂).mp h1

def ThetaFixMbSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), RigidIn a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.D.toPre.P.A),
      (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ P.oD.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂

def ThetaWeilSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F],
      (∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ oP.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂) →
      ∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂

def SerreAllSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A),
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂) → φ₁ = φ₂

def WeilRosatiSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (O : Type) [Ring O] [StarRing O] (o : P.OAct O)
    (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (a : O) (c : Γ(T.left, ⊤)ˣ), x ^ k = 1 → y ^ k = 1 →
    (Out.WeilIs P.A P.L k (x ≫ o.act a) y c ↔ Out.WeilIs P.A P.L k x (y ≫ o.act (star a)) c)

theorem thetaTriv (h1 : ThetaFixMbSt) (h2 : ThetaWeilSt) (h3 : SerreAllSt) : ThetaTrivSt := by
  intro E _ _ _ H D l c k _ bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  have hR0 := hR
  obtain ⟨hw₁, hw₂, -⟩ := hR0

  have hMb := h1 E H D l c k bF a t P hP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hR
  refine h3 E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ hw₁ hw₂ ?_
  intro F _ _ _ x hx
  exact h2 E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ hw₁ hw₂ F (hMb F) x hx

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Hom

variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

def preH {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) : (X ⟶ M) →* (Y ⟶ M) :=
  MonoidHom.mk' (f ≫ ·) fun a b => MonObj.comp_mul f a b

theorem pre_prod {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by
  have h := map_list_prod (preH (M := M) f) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

theorem scale_prodPts {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by
  unfold prodPts
  rw [pre_prod]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  have hs : (scaleD a).comp (scaleD (c i)) = scaleD ((a • c) i) := by
    apply AlgHom.ext
    intro x
    refine TrivSqZeroExt.ext ?_ ?_
    all_goals (simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, AlgHom.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Pi.smul_apply]; try ring)
  rw [← Category.assoc, spMap_comp, hs]

end Hom

section Push

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

def pushforwardHom : (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) :=
  MonoidHom.mk' (pushR G) fun a b => by
    show iotaB ≫ Geo.Tor.pushPt _ (a * b) = (iotaB ≫ Geo.Tor.pushPt _ a) * (iotaB ≫ Geo.Tor.pushPt _ b)
    rw [← MonObj.comp_mul]
    congr 1
    exact map_mul (Geo.Tor.pushHom (Geo.Tor.isGrpPullback_pullback G (fB R R')) _) a b

theorem pushR_prod {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by
  have h := map_list_prod (pushforwardHom (R := R) (R' := R') (P := P) G) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

end Push

theorem isGrpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by
  have hfst : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.fst G.hom f = F := pullback.lift_fst _ _ _
  have hsnd : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.snd G.hom f = G''.hom ≫ g := pullback.lift_snd _ _ _
  have hP := Geo.Tor.isGrpPullback_pullback G f
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback G.hom f)
    rw [hfst]
    exact h.1
  · intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · let x₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (x₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w x₀))
      let y₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (y₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w y₀))
      let x₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (x.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w x) =≫ (g ≫ f))
      let y₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (y.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w y) =≫ (g ≫ f))
      have e1 : (x₀' * y₀').left = (x₀ * y₀).left ≫ pullback.fst G.hom f :=
        hP.2 _ x₀ y₀ x₀' y₀' rfl rfl
      have e2 : (x₀'' * y₀'').left = (x * y).left ≫ F := h.2 T x y x₀'' y₀'' rfl rfl
      have e3 : (x₀' * y₀').left = (x₀'' * y₀'').left := by
        refine Geo.Tor.mul_left_congr (Category.assoc T.hom g f) x₀' y₀' x₀'' y₀'' ?_ ?_
        · show x₀.left ≫ pullback.fst G.hom f = x.left ≫ F
          rw [hx, Category.assoc, hfst]
        · show y₀.left ≫ pullback.fst G.hom f = y.left ≫ F
          rw [hy, Category.assoc, hfst]
      rw [Category.assoc, hfst, ← e1, e3, e2]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x * y)]
      exact Over.w (x₀ * y₀)

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

