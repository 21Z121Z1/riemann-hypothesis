import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AlgebraicPointWeights
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def WeightOverFields : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
      evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

def IntegralDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) →
      ∀ i : Ix Dw, ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t i : T.Fr)

def AlgebraicPointOver : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e ∧ T.FinRes ∧ Nonempty (letI := io.toAlgebra; FrPt Xo c T.Fr)

def IntegralFrameAfterExt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    letI := io.toAlgebra
    ∀ y : FrPt Xo c T.Fr, ∃ (T' : CDVR) (io' : c.F →+* T'.Fr),
      letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (r : ℕ), 0 < r ∧ (∀ x : T.Fr, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧
        φ.toRingHom.Finite ∧ (T.FinRes → T'.FinRes) ∧
        ∃ (z : FrPt Xo c T'.Fr) (y' : IntFr Xo c T' io') (t : Ix Dw → T'.Frˣ), FrMap φ y z ∧ FrBor t z y'.1

structure AlgebraicLaws : Prop where
  weight : WeightOverFields Xo c
  unitDiag : IntegralDiagUnit Xo c
  algPoint : AlgebraicPointOver Xo c
  intFrame : IntegralFrameAfterExt Xo c

variable {Xo c}

theorem unitIndep_of (h₁ : WeightOverFields Xo c) (h₂ : IntegralDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw : evI y' f = wchar (ex Dw a n) t * evI y f := h₁ a n f hf T.Fr t y.1 y'.1 hb
  choose u hu using h₂ T io y y' t hb
  have hU : (wchar (ex Dw a n) t : T.Fr) = algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V) := by
    simp [wchar, hu]
  rw [hw, hU, nval_mul_unit]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 (Units.ne_zero _)
  · have : valV T.V (algebraMap T.V T.Fr ((∏ i, u i ^ ex Dw a n i : T.Vˣ) : T.V)) = 1 := by
      unfold valV
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h (Units.isUnit _)
    simp only [vV, this, WithZero.log_one, neg_zero]

theorem intFrNe_of (h₁ : AlgebraicPointOver Xo c) (h₂ : IntegralFrameAfterExt Xo c) :
    IntFrNe Xo c (fun _ _ y => y.IsAlg) := by
  intro la
  obtain ⟨T, io, e, ho, hT, ⟨y⟩⟩ := h₁ la
  obtain ⟨T', io', φ, r, hr, hv, -, hfin, z, y', t, -, -⟩ := h₂ la T io e ho y
  letI := io.toAlgebra
  letI := io'.toAlgebra
  have hc : (φ : T.Fr →+* T'.Fr).comp io = io' := RingHom.ext fun x => φ.commutes x
  exact ⟨T', io', r * e, hc ▸ ho.bc (φ : T.Fr →+* T'.Fr) hr hv, y', hfin hT⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsSplitOff (l : Level H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'

variable {Xo : Moduli Dw l}

section Fibre

variable {Ω : Type} [CommRing Ω]

def toFib (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : T ⟶ Gx x :=
  (lift (Over.homMk t rfl : Over.mk (t ≫ x) ⟶ Over.mk x) a).left

def push {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : T ⟶ Xo.univ.t.G.left :=
  toFib x t a ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left

def Sends {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Prop :=
  (lift (𝟙 (Over.mk x)) a).left ≫ ψ = (lift (𝟙 (Over.mk x')) b).left

def IsLinHom {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') : Prop :=
  ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ∧
  (∀ (T : Scheme.{0}) (t : T ⟶ Sp Ω) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G)
      (b₁ b₂ : Over.mk (t ≫ x') ⟶ Xo.univ.t.G),
    b₁.left = push ψ t a₁ → b₂.left = push ψ t a₂ → (b₁ * b₂).left = push ψ t (a₁ * a₂)) ∧
  ∀ r : 𝓞 E, (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ ψ = ψ ≫ (Over.mk x' ◁ Xo.univ.t.act.act r).left

def IsLieImg (p : ℕ) {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x')
    (v w : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) : Prop :=
  IsTanAt x v ∧ IsTanAt x' w ∧
    ∃ a : tEps x ⟶ Xo.univ.t.G, a.left = v ∧
      spMap (epsMul (p : Ω)) ≫ w = push ψ (spMap (algebraMap Ω (DualNumber Ω))) a

def IsThGen (x : Sp Ω ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ s' : LB.Sec (PPx x), ∃! a : Ω, ∀ i, s'.f i = scal x a i * s.f i

end Fibre

def IsHeckeIsog (p : ℕ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') : Prop :=
  x' ≫ Xo.s = x ≫ Xo.s ∧ IsLinHom ψ ∧
  (∀ b, ∃ a, Sends ψ a b) ∧
  (∀ a, Sends ψ a 1 ↔ a ∈ C) ∧
  (∀ (n : ℕ) (a₁ a₂ : Over.mk x ⟶ Xo.univ.t.G) (b₁ b₂ : Over.mk x' ⟶ Xo.univ.t.G) (e : Ωˣ), n.Coprime p →
    Sends ψ a₁ b₁ → Sends ψ a₂ b₂ →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a₁ a₂ (unitOn e) →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n b₁ b₂ (unitOn (e ^ (p ^ 2)))) ∧
  (∀ a : Dw.La, Sends ψ (toUnit _ ≫ Xo.univ.eta a) (toUnit _ ≫ Xo.univ.eta (p • a))) ∧
  (∀ a : Dw.La, Sends ψ (toUnit _ ≫ Xo.univ.etaA a) (toUnit _ ≫ Xo.univ.etaA (p • a)))

variable (Xo) (c : Coeff l)

abbrev Transport : Type 1 :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X),
    (Gx x ⟶ Gx x') → LB.Sec (PPx x) → LB.Sec (PPx x') → Prop

variable {𝔓 : Ideal (𝓞 E)} {p : ℕ}

def HeckeIdx (_h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) : Type :=
  {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y.x) Dw 𝔓 p i C}

def IsHeckePt (tr : Transport Xo c) (h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : HeckeIdx Xo c h i Ω y) (z : FrPt Xo c Ω) : Prop :=
  ∃ ψ : Gx y.x ⟶ Gx z.x, IsHeckeIsog p C.1 ψ ∧ (∀ τ j, IsLieImg p ψ (y.u τ j) (z.u τ j)) ∧
    tr Ω y.x z.x ψ y.s z.s

def TrTotal (tr : Transport Xo c) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') (s : LB.Sec (PPx x)),
    x ≫ Xo.s = sOf c Ω → Xo.univ.t.HeckeKer (Over.mk x) Dw 𝔓 p i C → IsHeckeIsog p C ψ → IsThGen x s →
    ∃ s', IsThGen x' s' ∧ tr Ω x x' ψ s s'

def TrUnique (tr : Transport Xo c) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') (s : LB.Sec (PPx x)) (s' s'' : LB.Sec (PPx x')),
    x ≫ Xo.s = sOf c Ω → Xo.univ.t.HeckeKer (Over.mk x) Dw 𝔓 p i C → IsHeckeIsog p C ψ → IsThGen x s →
    IsThGen x' s' → IsThGen x' s'' → tr Ω x x' ψ s s' → tr Ω x x' ψ s s'' → s' = s''

def FinSt : Prop :=
  ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ),
    HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y)

def TotalSt : Prop :=
  ToroidalHeckeCompatibility (D := Dw) → ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c),
    TrTotal Xo c tr 𝔓 p i →
    HkTotal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y)
      (fun Ω _ _ _ y C z => IsHeckePt Xo c tr h i Ω y C z)

def FunSt : Prop :=
  ToroidalHeckeCompatibility (D := Dw) → ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c),
    TrUnique Xo c tr 𝔓 p i →
    HkFun (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y) (fun Ω _ _ _ y C z => IsHeckePt Xo c tr h i Ω y C z)

example {Ω : Type} [CommRing Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) : IsThGen y.x y.s := y.gen

example {Ω : Type} [CommRing Ω] (x : Sp Ω ⟶ Xo.X) (a : Over.mk x ⟶ Xo.univ.t.G) : Sends (𝟙 (Gx x)) a a := by
  simp [Sends]

example {Ω : Type} [CommRing Ω] (x : Sp Ω ⟶ Xo.X) : IsLinHom (𝟙 (Gx x)) := by
  have hp : ∀ (T : Scheme.{0}) (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G), push (𝟙 (Gx x)) t a = a.left := by
    intro T t a
    unfold push toFib
    rw [Category.id_comp, ← Over.comp_left, lift_snd]
  refine ⟨Category.id_comp _, fun T t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => by simp⟩
  rw [hp] at h₁ h₂ ⊢
  rw [Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂]

end GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def totalDeg (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def RowsDominant (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, Antitone fun i : Fin (Dw.mult τ) => a (τ, i)

def LastEntryPos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ ∃ i : Fin (Dw.mult τ), (i : ℕ) + 1 = Dw.mult τ ∧ 1 ≤ a (τ, i)

def IsLevelFactor (l : Level H) (al : 𝓞 E) (q : ℕ) : Prop :=
  al ∈ Algebra.adjoin ℤ {H.w0} ∧ al * H.bar al = (q : 𝓞 E) ∧ Odd q ∧ q ∣ l.M ∧ IsCoprime al (H.bar al) ∧
    l.Mb ≤ Ideal.span {H.bar al}

def InJetRange (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ) : Prop :=
  RowsDominant Dw a ∧ Dw.p + Dw.q ≤ n ∧ IsLevelFactor l al q ∧ totalDeg Dw a + 2 ≤ q

section Rig

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def rigAtOrigin (T : Over X) (k : ℤ) :
    LB.Gen (LB.LinComb L.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => k)) :=
  rigT A L.L L.rig T k

end Rig

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def ValuesExistUnique (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v : S, ThValAt Xo c nab y x P v

def GeneratorsCuspidal (nab : NabV Xo c)
    (Cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), RowsDominant Dw a → Even n → LastEntryPos Dw a →
    ∀ f ∈ thGen Xo c nab a n, f ∈ Cusp a n

def SomeGeneratorNeZero (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ), InJetRange Dw l a n al q →
    ∃ f ∈ thGen Xo c nab a n, f ≠ 0

def NoCommonZero (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ), InJetRange Dw l a n al q →
    ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)),
      ∃ (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n ∧
        (∀ b, KilledBy Xo (Ideal.span {H.bar al}) (levPt Xo y.x (x b))) ∧
        (∃ v, ThValAt Xo c nab y x P v) ∧ ∀ v, ThValAt Xo c nab y x P v → v ≠ 0

def OrderZero (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F 1 (rigAtOrigin Xo.univ.t.G Xo.univ.t.PP (ptO Xo y.x) k)
      (toΓ S (nab y k F 0))

def ThetaClaims (nab : NabV Xo c) (Cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ValuesExistUnique Xo c nab ∧ GeneratorsCuspidal Xo c nab Cusp ∧ SomeGeneratorNeZero Xo c nab ∧ OrderZero Xo c nab

end GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct

abbrev Fin𝔸 (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev Inf𝔸 (F : Type) [Field F] [NumberField F] : Type := InfiniteAdeleRing F

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}

section Lattices

variable (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)

def toFin (v : W) : Fin n → Fin𝔸 F ⊗[F] E := fun i => 1 ⊗ₜ fr.repr v i

def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L, z = fun i => a ⊗ₜ fr.repr x i}

def latAd (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {w | ∃ a ∈ 𝔄, ∃ z ∈ latHat F fr L, w = ((1 : Fin𝔸 F) ⊗ₜ[F] a) • g.1.mulVec z}

def latG (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : Submodule (𝓞 E) W :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : W, (∃ z ∈ latHat F fr L, toFin F fr x = g.1.mulVec z) ∧ v = a • x}

def latBase : Submodule (𝓞 E) W := Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x ∈ L, v = a • x}

omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W] in

theorem latBase_le_latG_one : latBase L 𝔄 ≤ latG F fr L 𝔄 1 := by
  refine Submodule.span_mono ?_
  rintro v ⟨a, ha, x, hx, rfl⟩
  refine ⟨a, ha, x, ⟨toFin F fr x, AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩, ?_⟩, rfl⟩
  simp

def CongrAt (M : ℕ) (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) (u v : W) : Prop :=
  ∃ y ∈ latAd F fr L 𝔄 g, toFin F fr v - g.1.mulVec (toFin F fr u) = M • y

end Lattices

section Datum

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def half (Dw : Datum H) (l : Level H) : Submodule (𝓞 E) Dw.La :=
  l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La)

def IsLatEmb (h : W → W → E) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (Dw : Datum H)
    (ι : Dw.La →ₗ[𝓞 E] W) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latBase L 𝔄 ∧
    ∃ ε : ℤˣ, ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ E (ξ₀ * h (ι x) (ι y))

end Datum

section Model

def crd (hr : n = r) (fr : Module.Basis (Fin n) E W) (v : W) : Fin r → E := fun i => fr.repr v ((finCongr hr).symm i)

def vec (hr : n = r) (fr : Module.Basis (Fin n) E W) (x : Fin r → E) : W := ∑ i, x (finCongr hr i) • fr i

def IsModelOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (ξ₀ : E)
    (q : ℕ) (X : Data E r) : Prop :=
  (∀ x y : W, herm X.Gm (crd hr fr x) (crd hr fr y) = -h x y) ∧ X.p0 = q ∧
    (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) ∧
    (X.ξ0 = ξ₀ ∨ X.ξ0 = -ξ₀) ∧ ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0

def IsOrthoFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def IsArchAt (τ : E →+* ℂ) (th : Inf𝔸 F ⊗[F] E →+* ℂ) : Prop :=
  (∀ e : E, th (1 ⊗ₜ e) = τ e) ∧ Continuous fun a : Inf𝔸 F => th (a ⊗ₜ 1)

def IsRatUnitary (fr : Module.Basis (Fin n) E W) (h : W → W → E) (γ : GL (Fin n) E) : Prop :=
  ∀ x y : Fin n → E, h (fr.equivFun.symm (γ.1.mulVec x)) (fr.equivFun.symm (γ.1.mulVec y)) =
    h (fr.equivFun.symm x) (fr.equivFun.symm y)

def ratTo (A : Type) [CommRing A] [Algebra F A] (γ : GL (Fin n) E) : GL (Fin n) (A ⊗[F] E) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom γ

end Model

section Pin

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

def LatMark (hr : n = r) (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)
    (l : Level H) (ι : Dw.La →ₗ[𝓞 E] W) (X : Data E r) (mk : Dw.La → X.Λ) (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : Prop :=
  (∀ v : W, crd hr fr v ∈ X.Λ ↔ v ∈ latG F fr L 𝔄 g) ∧
    ∀ a ∈ half Dw l, CongrAt F fr L 𝔄 l.M g (ι a) (vec hr fr (mk a : Fin r → E))

def IsMarkStab (l : Level H) (X : Data E r) (mk : Dw.La → X.Λ) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧
    ∀ a ∈ half Dw l, ∃ y ∈ X.Λ, γ.1.mulVec (mk a : Fin r → E) - (mk a : Fin r → E) = l.M • y

def IsLevelStab (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 E] W) {G : Type} [Group G] (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E))
    (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E)) (Kf : Subgroup G) : Prop :=
  ∀ k, k ∈ Kf ↔ inf k = 1 ∧ latAd F fr L 𝔄 (fin k) = latAd F fr L 𝔄 1 ∧
    ∀ a ∈ half Dw l, CongrAt F fr L 𝔄 l.M (fin k) (ι a) (ι a)

def IsDictOf (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (l : Level H) (ι : Dw.La →ₗ[𝓞 E] W) {Comp : Type} (X : Comp → Data E r)
    (mk : ∀ k, Dw.La → (X k).Λ) (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) {G : Type} (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E))
    (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E)) (dict : G → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g, ∃ γ : GL (Fin n) E, IsRatUnitary fr h γ ∧
    LatMark F hr fr L 𝔄 l ι (X (dict g).1) (mk (dict g).1) (ratTo F (Fin𝔸 F) γ * fin g) ∧
    ∀ τ : (X (dict g).1).Ψ, mat (dict g).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) ((ratTo F (Inf𝔸 F) γ * inf g).1.map (th τ.1)) * x₀ τ.1

def IsFamilyOf (U : Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((Fm.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
  ∀ k (x : (U.X k).dom), ∃ P : (Fm.Di (ik k)).La →+ (Fin g → ℂ),
    (∀ a j, P a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    IsPeriod (Fm.Di (ik k)) (fun j => relab c σ (e j).1) P ∧ (U.un k x).x = Fm.u (ik k) P ∧
    ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fm.ex (ik k) P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      ((U.un k x).u τ i)

def AdPin (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (U : Unf Xo c σ r) {G : Type} [Group G]
    (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E)) (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E))
    (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G) : Prop :=
  ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (ι : Dw.La →ₗ[𝓞 E] W) (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    IsFamilyOf U e Fm ik φ ∧ IsLatEmb h L 𝔄 ξ₀ Dw ι ∧ (∀ τ, IsArchAt F τ (th τ)) ∧
    (∀ k, IsModelOf H hr fr h ξ₀ Dw.q (U.X k) ∧ IsOrthoFrame (U.X k) x₀ ∧
      IsMarkStab l (U.X k) (fun a => φ k (Fm.t (ik k) a)) ∧
      ∃ gk : G, LatMark F hr fr L 𝔄 l ι (U.X k) (fun a => φ k (Fm.t (ik k) a)) (fin gk)) ∧
    IsLevelStab F fr L 𝔄 l ι inf fin Kf ∧
    IsDictOf F hr fr h L 𝔄 l ι U.X (fun k a => φ k (Fm.t (ik k) a)) th x₀ inf fin dict

end Pin

section Adelic

def unitaryOver (cj : E ≃ₐ[F] E) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (A : Type) [CommRing A] [Algebra F A] :
    Subgroup (GL (Fin n) (A ⊗[F] E)) :=
  let B : (Fin n → A ⊗[F] E) → (Fin n → A ⊗[F] E) → A ⊗[F] E := fun x y =>
    ∑ a, ∑ b, x a * ((1 : A) ⊗ₜ[F] h (fr a) (fr b)) * Algebra.TensorProduct.map (AlgHom.id F A) (cj : E →ₐ[F] E) (y b)
  { carrier := {g | ∀ x y, B (g.1.mulVec x) (g.1.mulVec y) = B x y}
    one_mem' := fun x y => by simp
    mul_mem' := fun {a b} ha hb x y => by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
    inv_mem' := fun {a} ha x y => by
      have := ha (a⁻¹.1.mulVec x) (a⁻¹.1.mulVec y)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this.symm }

abbrev AdelicU (cj : E ≃ₐ[F] E) (fr : Module.Basis (Fin n) E W) (h : W → W → E) : Type :=
  unitaryOver F cj fr h (Inf𝔸 F) × unitaryOver F cj fr h (Fin𝔸 F)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

def AdPinU (cj : E ≃ₐ[F] E) (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (U : Unf Xo c σ r)
    (dict : AdelicU F cj fr h → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup (AdelicU F cj fr h)) : Prop :=
  (∀ x, cj x = cc x) ∧ (∀ x : E, cc x = x → x ∈ Set.range (algebraMap F E)) ∧
    AdPin F hr fr h L 𝔄 ξ₀ U (fun g => g.1.1) (fun g => g.2.1) dict Kf

end Adelic

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
end
end

