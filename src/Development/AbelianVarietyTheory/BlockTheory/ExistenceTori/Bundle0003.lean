import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def stdForm (x y : Fin n → E) : E := ∑ j, x j * IsCMField.complexConj E (y j)

def stdMod (E : Type) [Field E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

structure Lat (E : Type) [Field E] (n : ℕ) where
  L : Submodule (𝓞 E) (Fin n → E)
  fg : L.FG
  span_top : Submodule.span E (L : Set (Fin n → E)) = ⊤

omit [NumberField E] [IsCMField E] in
theorem mem_stdMod {x : Fin n → E} : x ∈ stdMod E n ↔ ∀ j, ∃ a : 𝓞 E, (a : E) = x j := by
  simp only [stdMod, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdMod (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdMod E n := by
  rw [mem_stdMod]
  intro i
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

def Lat.std (E : Type) [Field E] (n : ℕ) : Lat E n where
  L := stdMod E n
  fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  span_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using single_mem_stdMod j

def Lat.inter (Λ : Lat E n) : Submodule (𝓞 E) (Fin n → E) := stdMod E n ⊓ Λ.L

def Lat.SelfDual (Λ : Lat E n) : Prop :=
  ∀ x : Fin n → E, x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ a : 𝓞 E, (a : E) = stdForm x y

def EqAtPrime (p : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (∀ x ∈ L₁, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₂) ∧ ∀ x ∈ L₂, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₁

def Lat.StdAt (Λ : Lat E n) (s : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ s → EqAtPrime p Λ.L (stdMod E n)

def mulStd (E : Type) [Field E] (n N : ℕ) : Submodule (𝓞 E) (Fin n → E) := (N : 𝓞 E) • stdMod E n

def Lat.Admissible (Λ : Lat E n) (M N : ℕ) : Prop :=
  Odd N ∧ M ∣ N ∧ mulStd E n N ≤ Λ.inter

def Lat.cardCenterZero (Λ : Lat E n) (r N : ℕ) : ℕ :=
  (mulStd E n N).toAddSubgroup.relIndex Λ.inter.toAddSubgroup ^ r

def Lat.cardZ (Λ : Lat E n) (r N : ℕ) : ℕ :=
  (mulStd E n N).toAddSubgroup.relIndex Λ.L.toAddSubgroup ^ r

def halfPart {H : Host E} (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ⨅ k : ℕ, Ideal.span {(N : 𝓞 E)} ⊔ l.Mb ^ k

def IsUnitary (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop := ∀ x y, stdForm (γ x) (γ y) = stdForm x y

def Lat.map (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Lat E n where
  L := Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E))
  fg := Λ.fg.map _
  span_top := by
    have h : ((Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        γ.toLinearMap '' (Λ.L : Set (Fin n → E)) := rfl
    rw [h, ← Submodule.map_span, Λ.span_top, Submodule.map_top, LinearEquiv.range]

def Lat.InGenus (Λ : Lat E n) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
    IsUnitary γ ∧ EqAtPrime p Λ.L ((Lat.std E n).map γ).L

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def letter (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) : MvPolynomial (LtN Dw n) c.F :=
  ∑ j, C (embF c σ (b j)) * X ⟨σ, i, j⟩

def symLat (Λ : Lat E n) : Subalgebra (integralClosure ℤ c.F) (MvPolynomial (LtN Dw n) c.F) :=
  Algebra.adjoin (integralClosure ℤ c.F) {P | ∃ σ i, ∃ b ∈ Λ.L, P = letter Dw c σ i b}

def harmSpace (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def harmLat (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n) : Set (MvPolynomial (LtN Dw n) c.F) :=
  {P | P ∈ harmSpace Dw c a n ∧ P ∈ symLat Dw c Λ}

def push (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letter Dw c ℓ.1 ℓ.2.1 (γ (Pi.single ℓ.2.2 1))

def HarmLatFGFull : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n),
    (∃ S : Submodule (integralClosure ℤ c.F) (MvPolynomial (LtN Dw n) c.F),
      S.FG ∧ (S : Set (MvPolynomial (LtN Dw n) c.F)) = harmLat Dw c a Λ) ∧
    ∀ P ∈ harmSpace Dw c a n, ∃ k : ℕ, 0 < k ∧ k • P ∈ harmLat Dw c a Λ

def HarmLatStd : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), harmLat Dw c a (Lat.std E n) = harmA c a n

def HarmLatPush : Prop :=
  ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)), IsUnitary γ →
    push Dw c γ '' harmLat Dw c a Λ = harmLat Dw c a (Λ.map γ)

abbrev TorsSq (n N : ℕ) : Type :=
  Fin n → Dw.La ⧸ (Ideal.span {(N : 𝓞 E) ^ 2} • (⊤ : Submodule (𝓞 E) Dw.La))

def killed (N : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ L) :
    Set (TorsSq Dw n N) :=
  {t | ∀ μ : L →ₗ[𝓞 E] (Fin n → 𝓞 E), ∀ i, ∑ j, μ ⟨_, hN j⟩ i • t j = 0}

def CardZClaim : Prop :=
  ∀ (n M N : ℕ) (Λ : Lat E n), Λ.SelfDual → Λ.Admissible M N →
    ∀ (h₀ : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter) (h : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Λ.L),
      Nat.card (killed Dw N Λ.inter h₀) = Λ.cardCenterZero (Dw.p + Dw.q) N ∧
      Nat.card (killed Dw N Λ.L h) = Λ.cardZ (Dw.p + Dw.q) N ∧
      0 < Λ.cardCenterZero (Dw.p + Dw.q) N ∧ 0 < Λ.cardZ (Dw.p + Dw.q) N

end Poly

def GenusIffSelfDual (_H : Host E) : Prop := ∀ (n : ℕ) (Λ : Lat E n), Λ.InGenus ↔ Λ.SelfDual

def AdmissibleExists {H : Host E} (l : Level H) : Prop :=
  ∀ (n s : ℕ) (Λ : Lat E n), Λ.StdAt (2 * s) → s.Coprime l.M → ∃ N, Λ.Admissible l.M N ∧ N.Coprime s

def Lat.IsMarking (Λ : Lat E n) (I : Ideal (𝓞 E)) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ I)) : Prop :=
  Function.Surjective φ ∧ LinearMap.ker φ = I • (⊤ : Submodule (𝓞 E) Λ.L)

def RepresentativeExists {H : Host E} (l : Level H) : Prop :=
  ∀ (n s N : ℕ) (Λ : Lat E n) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), s ≠ 0 → N ≠ 0 → Λ.InGenus →
    Λ.IsMarking (halfPart l N) φ →
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), IsUnitary γ ∧ (Λ.map γ).StdAt (s * l.M) ∧
      ∀ (x : Λ.L) (y : Fin n → 𝓞 E), (∀ j, γ x j = (y j : E)) → ∀ j, φ x j = Ideal.Quotient.mk _ (y j)

def ClassesFinite {H : Host E} (l : Level H) : Prop :=
  ∀ (n N : ℕ), N ≠ 0 →
    ∃ T : Set (Σ Λ : Lat E n, Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), T.Finite ∧
      ∀ (Λ : Lat E n) (φ : Λ.L →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ halfPart l N)), Λ.InGenus → Λ.IsMarking (halfPart l N) φ →
        ∃ t ∈ T, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), IsUnitary γ ∧ (Λ.map γ).L = t.1.L ∧
          ∀ (x : Λ.L) (y : t.1.L), γ x = y → φ x = t.2 y

theorem std_selfDual : (Lat.std E n).SelfDual := by
  intro x
  change x ∈ stdMod E n ↔ ∀ y ∈ stdMod E n, _
  constructor
  · intro hx y hy
    rw [mem_stdMod] at hx hy
    choose a ha using hx
    choose b hb using hy
    refine ⟨∑ j, a j * IsCMField.ringOfIntegersComplexConj E (b j), ?_⟩
    simp [stdForm, ← ha, ← hb]
  · intro h
    rw [mem_stdMod]
    intro j
    obtain ⟨a, ha⟩ := h _ (single_mem_stdMod j)
    refine ⟨a, ?_⟩
    rw [ha]
    simp [stdForm, Pi.single_apply, apply_ite]

omit [NumberField E] [IsCMField E] in
theorem std_stdAt (s : ℕ) : (Lat.std E n).StdAt s := by
  intro p hp _
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  exact ⟨fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩, fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩⟩

theorem std_admissible {H : Host E} (l : Level H) : (Lat.std E n).Admissible l.M l.M := by
  refine ⟨l.odd, dvd_rfl, ?_⟩
  intro x hx
  change x ∈ stdMod E n ⊓ stdMod E n
  rw [inf_idem]
  rw [mulStd, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (stdMod E n).smul_mem _ hy

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneralizedScalarsNumberField
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Relations

variable {Xo : Moduli Dw l} {c : Coeff l}

def GenScal {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ h : y'.x = y.x, ∀ i, (h ▸ y'.s : LB.Sec (PPx y.x)).f i = scal y.x a i * y.s.f i

def LieChange {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) : Prop :=
  ∀ i, IsCombAt y.x (y.u τ) (fun j => M i j) (y'.u τ i)

end Relations

section Claims

variable (Xo : Moduli Dw l) (c : Coeff l)

def BaseChangeField : Prop :=
  ∀ (S T : Type) [Field S] [Algebra c.F S] [Field T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

def ReframeIntegral : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → y'.x = y.x →
      ∃ (t : Ix Dw → T.Frˣ) (z : FrPt Xo c T.Fr), FrBor t y' z ∧ Integral T io z

def ReframeIntFr : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    letI := io.toAlgebra
    ∀ y' : FrPt Xo c T.Fr, y'.x = y.1.x →
      ∃ (t : Ix Dw → T.Frˣ) (z : IntFr Xo c T io), FrBor t y' z.1

def PointNumberField : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧
    ∃ x : Sp L ⟶ Xo.X, x ≫ Xo.s = sOf c L

def FramedPointNumberField : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ Nonempty (FrPt Xo c L)

def CombLinearAt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (m : ℕ)
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, IsTanAt x (v i)) →
    (∀ cf : Fin m → S, ∃! w, IsCombAt x v cf w) ∧
    (∀ (cf : Fin m → S) w, IsCombAt x v cf w → IsTanAt x w) ∧
    (∀ τ : E →+* ℂ, (∀ i, IsEigAt c τ (v i)) → ∀ (cf : Fin m → S) w, IsCombAt x v cf w → IsEigAt c τ w) ∧
    (∀ i, IsCombAt x v (Pi.single i 1) (v i)) ∧
    ∀ (n : ℕ) (M : Fin n → Fin m → S) (w : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)),
      (∀ j, IsCombAt x v (M j) (w j)) →
      ∀ (b : Fin n → S) z, IsCombAt x w b z → IsCombAt x v (fun i => ∑ j, b j * M j i) z

def GenRatio : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), y'.x = y.x →
    (∃! a : S, GenScal a y y') ∧ ∀ a : S, GenScal a y y' → IsUnit a

def IntLieGL : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → Integral T io y' → y'.x = y.x →
      ∀ τ : E →+* ℂ, ∃ M : GL (Fin (Dw.mult τ)) T.V,
        LieChange τ ((M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V).map (algebraMap T.V T.Fr)) y y'

def IntGenUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → Integral T io y' → y'.x = y.x →
      ∃ a : T.Vˣ, GenScal (algebraMap T.V T.Fr (a : T.V)) y y'

def IntFrameGL : Prop := IntLieGL Xo c ∧ IntGenUnit Xo c

end Claims

def CombLinear : Prop :=
  ∀ (V R : Type) [CommRing V] [CommRing R] [Algebra V R] (G : Over (Sp V)) [GrpObj G] (m : ℕ)
    (v : Fin m → (epsOver V R ⟶ G)), (∀ i, IsTan (v i)) →
    (∀ cf : Fin m → R, ∃! w, IsComb v cf w) ∧
    (∀ (cf : Fin m → R) w, IsComb v cf w → IsTan w) ∧
    (∀ i, IsComb v (Pi.single i 1) (v i)) ∧
    ∀ (n : ℕ) (M : Fin n → Fin m → R) (w : Fin n → (epsOver V R ⟶ G)), (∀ j, IsComb v (M j) (w j)) →
      ∀ (b : Fin n → R) z, IsComb w b z → IsComb v (fun i => ∑ j, b j * M j i) z

def Claims (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  BaseChangeField Xo c ∧ ReframeIntegral Xo c ∧ ReframeIntFr Xo c ∧ PointNumberField Xo c ∧
    FramedPointNumberField Xo c ∧ CombLinearAt Xo c ∧ CombLinear ∧ GenRatio Xo c ∧ IntFrameGL Xo c

section Basic₂

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem pointNumberField_of_framed (h : FramedPointNumberField Xo c) : PointNumberField Xo c := by
  obtain ⟨L, _, _, hL, ⟨y⟩⟩ := h
  exact ⟨L, inferInstance, inferInstance, hL, y.x, y.x_over⟩

theorem genScal_existsUnique {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (h : y'.x = y.x) :
    ∃! a : S, GenScal a y y' := by
  obtain ⟨a, ha, hu⟩ := y.gen (h ▸ y'.s)
  exact ⟨a, ⟨h, ha⟩, fun b ⟨_, hb⟩ => hu b hb⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HarmonicChartValues
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

section Formal

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def monVal (B : Germ.FB S d O) (h : Germ.PS S 2 d) (w0 : O) (k : ℤ) (f : Germ.PS S 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → S) (α : κ →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff
    (Germ.DmonOf (B.FK S) u α (f * Germ.FB.expS S ((k : S) • B.hL S h w0)))

theorem monVal_natCast (B : Germ.FB S d O) (h : Germ.PS S 2 d) (w0 : O) (m : ℕ) (f : Germ.PS S 1 d)
    {κ : Type} [Fintype κ] (u : κ → Fin d → S) (α : κ →₀ ℕ) :
    monVal B h w0 (m : ℤ) f u α = B.nabVal S h w0 m f u (MvPolynomial.monomial α 1) := by
  classical
  nontriviality S
  simp [monVal, Germ.FB.nabVal, Germ.DpolyOf, MvPolynomial.support_monomial]

def IsBalBilin (B : Germ.FB S d O) (β : Germ.PS S 2 d) : Prop :=
  Germ.ev (n := 3) ![Germ.addOf (B.FK S) (Germ.pt S d 0) (Germ.pt S d 1), Germ.pt S d 2] β =
      Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 2] β + Germ.ev (n := 3) ![Germ.pt S d 1, Germ.pt S d 2] β ∧
    Germ.ev (n := 3) ![Germ.pt S d 0, Germ.addOf (B.FK S) (Germ.pt S d 1) (Germ.pt S d 2)] β =
      Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 1] β + Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 2] β ∧
    Germ.ev (n := 2) ![Germ.pt S d 1, Germ.pt S d 0] β = β ∧
    ∀ a : O, Germ.ev (n := 2) ![Germ.comp1 (B.actK S a) (Germ.pt S d 0), Germ.pt S d 1] β =
      Germ.ev (n := 2) ![Germ.pt S d 0, Germ.comp1 (B.actK S (star a)) (Germ.pt S d 1)] β

def GaugeDiffSt (B : Germ.FB S d O) : Prop :=
  ∀ h h' : Germ.PS S 2 d, B.IsCanonGauge S h → B.IsCanonGauge S h' → IsBalBilin B (h' - h)

end Formal

section Rig

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S] {G : Over X₀} [GrpObj G] [IsCommMonObj G]
  {x : Sp S ⟶ X₀} {d : ℕ}

def IsRigAtZero (L : RigLB G) {j : JetPts G x d} (eL : FrameL G x L.L j) : Prop :=
  ∀ m, LB.Gen.Corr L.L _ _ _ _
    (LB.pullGen L.L _ _ (eL m) (algMap x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S)).left)
    (Out.rigT G L.L L.rig (algO x S) 1)

end Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} (c : Coeff l)

@[reducible] def ratAlg (S : Type) [CommRing S] [Algebra c.F S] : Algebra ℚ S :=
  ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra

variable {c} {S : Type} [CommRing S] [Algebra c.F S]

abbrev FBar (H : Host E) (S : Type) [CommRing S] (d : ℕ) : Type :=
  @Germ.FB S _ d (𝓞 E) _ H.starRing

def letVec (y : FrPt Xo c S) (ℓ : Lt1 Dw) : Sp (DualNumber S) ⟶ Xo.univ.t.G.left := y.u ℓ.1 ℓ.2

def IsGaugedChart (y : FrPt Xo c S) {d : ℕ} (j : JetPts Xo.univ.t.G y.x d)
    (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
    (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  IsChartOf Xo.univ.t y.x j B.G B.A (letVec y) cf ∧
    Realises Xo.univ.t y.x j e B ∧
    B.IsCanonGauge S h ∧
    IsFrameL Xo.univ.t y.x j e (B.A.act H.w0) eL ∧
    IsRigAtZero Xo.univ.t.PP eL

def chartVal (c : Coeff l) [Algebra c.F S] {d : ℕ} (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
    (h : Germ.PS S 2 d) (k : ℤ) (f : Germ.PS S 1 d) (α : Lt1 Dw →₀ ℕ) : S :=
  letI := H.starRing
  letI := ratAlg c S
  monVal B h H.w0 k f cf α

abbrev SecAt (y : FrPt Xo c S) (k : ℤ) : Type :=
  LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))

def IsNablaAt (y : FrPt Xo c S) (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : Prop :=
  ∃ (d : ℕ) (j : JetPts Xo.univ.t.G y.x d) (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d)
    (cf : Lt1 Dw → Fin d → S) (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j),
    IsGaugedChart y j e B cf h eL ∧
      ∀ (k : ℤ) (F : SecAt y k), ∃ f : Germ.PS S 1 d, IsGermIn eL k F f ∧
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = chartVal c B cf h k f α

variable (Xo c)

def IsNablaPin (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), IsNablaAt y fun k F α => nab y k F α

variable {Xo}

def polyVal {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (v : Fin n → (Lt1 Dw →₀ ℕ) → S) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, v b (colOf m b)

def Harm (Dw : Datum H) (n : ℕ) : Submodule c.F (MvPolynomial (LtN Dw n) c.F) :=
  harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun _ => 1

variable (Xo)

def ChartExistsSt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
    ∃ (d : ℕ) (j : JetPts Xo.univ.t.G y.x d) (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d)
      (cf : Lt1 Dw → Fin d → S) (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j),
      IsGaugedChart y j e B cf h eL

def PinExistsSt : Prop := ∃ nab : NabV Xo c, IsNablaPin Xo c nab

def HarmIndepSt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (v v' : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S), IsNablaAt y v → IsNablaAt y v' →
    ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n → ∀ (k : ℤ) (F : Fin n → SecAt y k),
      polyVal c P (fun b => v k (F b)) = polyVal c P fun b => v' k (F b)

def PinHarmSt : Prop :=
  ∀ nab : NabV Xo c, IsNablaPin Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ) (j : JetPts Xo.univ.t.G y.x d)
      (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
      (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j), IsGaugedChart y j e B cf h eL →
      ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n →
        ∀ (k : ℤ) (F : Fin n → SecAt y k) (f : Fin n → Germ.PS S 1 d), (∀ b, IsGermIn eL k (F b) (f b)) →
          polyVal c P (fun b => nab y k (F b)) = polyVal c P fun b => chartVal c B cf h k (f b)

def PinBaseChangeSt : Prop :=
  ∀ nab : NabV Xo c, IsNablaPin Xo c nab →
    ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z →
      ∀ g : ptO Xo z.x ⟶ ptO Xo y.x, g.left = spMap φ.toRingHom →
      ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n →
        ∀ (k : ℤ) (F : Fin n → SecAt y k) (F' : Fin n → SecAt z k),
          (∀ b, Out.IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (g ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) →
          φ (polyVal c P fun b => nab y k (F b)) = polyVal c P fun b => nab z k (F' b)

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues
end
end

