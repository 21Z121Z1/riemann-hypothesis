import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts

open Formalism.BasicNotions.TH MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

def nextRow {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : i.1 + 1 < l then a ⟨i.1 + 1, h⟩ else 0

def minorProd {R : Type} [CommRing R] {n l : ℕ} (a : Fin l → ℕ) (y : Matrix (Fin n) (Fin l) R)
    (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) : R :=
  ∏ i : Fin l, (y.submatrix (row i) (Fin.castLE i.2)).det ^ (a i - nextRow a i)

def topRows {n l : ℕ} (h : l ≤ n) (i : Fin l) (c : Fin (i.1 + 1)) : Fin n := ⟨c.1, by omega⟩

def botRows {n l : ℕ} (h : l ≤ n) (i : Fin l) (c : Fin (i.1 + 1)) : Fin n := ⟨n - (i.1 + 1) + c.1, by omega⟩

def zPlus (p q n : ℕ) : Matrix (Fin n) (Fin p) (Pol p q n 0) :=
  Matrix.of fun c a => MvPolynomial.X (Sum.inl a, Sum.inl c)

def zMinus (p q n : ℕ) : Matrix (Fin n) (Fin q) (Pol p q n 0) :=
  Matrix.of fun c b => MvPolynomial.X (Sum.inr b, Sum.inl c)

def delta {p q n : ℕ} (h : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Pol p q n 0 :=
  minorProd ap (zPlus p q n) (topRows (by omega)) * minorProd am (zMinus p q n) (botRows (by omega))

def wtK {p q : ℕ} (n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Ix p q → ℚ
  | .inl i => (ap i : ℚ) + (n : ℚ) / 2
  | .inr j => -(am j.rev : ℚ) - (n : ℚ) / 2

def wtExt {p q : ℕ} (n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Ix p q → ℚ
  | .inl i => (ap i : ℚ) + (n : ℚ) / 2
  | .inr j => -(am j : ℚ) - (n : ℚ) / 2

def wtH {p q : ℕ} (n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Ix n 0 → ℚ
  | .inl c => (if h : c.1 < p then (ap ⟨c.1, h⟩ : ℚ)
      else if h' : c.rev.1 < q then -(am ⟨c.rev.1, h'⟩ : ℚ) else 0) + ((p : ℚ) - (q : ℚ)) / 2
  | .inr c => c.elim0

def hcParam {p q : ℕ} (n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Ix p q → ℚ
  | .inl i => (ap i : ℚ) + ((p : ℚ) - ((i.1 : ℚ) + 1)) + (((n : ℚ) - p - q) + 1) / 2
  | .inr l => -(am l.rev : ℚ) - ((l.1 : ℚ) + 1) - (((n : ℚ) - p - q) - 1) / 2

def KilledByLower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : Prop :=
  ∀ (a : Fin p) (b : Fin q), act (Eab (Sum.inr b) (Sum.inl a)) v = 0

def IsLowestType {p q : ℕ} (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V) : Prop :=
  IrrGK M ∧ FiniteDimensional ℂ W ∧ KStable M.act W ∧
  (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) ∧
  (∃ e ∈ W, IsHW M.act Λ e) ∧
  (∀ e, e ∈ W ↔ OfType M.act Λ e) ∧
  (∀ e ∈ W, KilledByLower M.act e) ∧
  GlobalTheory.FockAlg.genSub M.act (W : Set M.V) = ⊤ ∧
  (∀ (μ : Ix p q → ℚ) (x : M.V), x ≠ 0 → x ∈ wtSub M.act μ →
    ∃ m : ℕ, ∑ i, μ (Sum.inl i) = ∑ i, Λ (Sum.inl i) + m ∧ (m = 0 ↔ x ∈ W))

def HasParam {p q : ℕ} {T : GrpData p q} (D : DSRep T) (lam : Ix p q → ℚ) : Prop :=
  IsParam lam ∧ Module.finrank ℂ ↥(hwSub D.HK.act (blattner lam)) = 1 ∧
  (∀ x, casimir D.HK.act x = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • x) ∧
  GlobalTheory.FockAlg.ConeTypes D.HK lam

def decay {p q : ℕ} (n : ℕ) (X : Mat p q) : ℝ :=
  ∏ i ∈ Finset.range (min p q),
    (Real.cosh ((Matrix.toEuclideanLin X.toBlocks₁₂).singularValues i) ^ n)⁻¹

section Maps

variable {p q n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

def IsKIntw (F : FockData T0 T1 T2) (M1 : GKMod p q) (W : Submodule ℂ M1.V) (M : GKMod n 0)
    (io : W ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) : Prop :=
  (∀ Z, IsKC Z → ∀ (e e' : W) (v : M.V), (e' : M1.V) = M1.act Z e →
    F.act1 Z (io (e ⊗ₜ v)) = io (e' ⊗ₜ v)) ∧
  ∀ Y (e : W) (v : M.V), F.act2 Y (io (e ⊗ₜ v)) = io (e ⊗ₜ M.act Y v)

def IsGIntw (F : FockData T0 T1 T2) (M1 : GKMod p q) (M : GKMod n 0)
    (I : M1.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) : Prop :=
  (∀ Z x v, F.act1 Z (I (x ⊗ₜ v)) = I (M1.act Z x ⊗ₜ v)) ∧
  ∀ Y x v, F.act2 Y (I (x ⊗ₜ v)) = I (x ⊗ₜ M.act Y v)

def HarmonicMaps (F : FockData T0 T1 T2) (D : DSRep T1) (W : Submodule ℂ D.HK.V) (τ : URep T2)
    (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (Δ : Pol p q n 0) (e0 : W) (v0 : M.V)
    (io : W ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) : Prop :=

  (io (e0 ⊗ₜ v0) = Δ) ∧

  (IsKIntw F D.HK W M io) ∧

  (∀ io', IsKIntw F D.HK W M io' → io' (e0 ⊗ₜ v0) = Δ → io' = io) ∧

  (∀ k ∈ T1.Kset, ∀ (h : T2.G) (e e' : W) (v v' : M.V),
    D.ι e' = D.U.π k (D.ι e) → j v' = τ.π h (j v) →
    F.π (k, h) (F.ι (io (e ⊗ₜ v))) = F.ι (io (e' ⊗ₜ v'))) ∧

  (∀ (e e' : W) (v v' : M.V), inner ℂ (F.ι (io (e' ⊗ₜ v'))) (F.ι (io (e ⊗ₜ v))) =
    ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι e') (D.ι e) * inner ℂ (j v') (j v)) ∧

  (∀ y, KilledByLower F.act1 (io y)) ∧

  (∀ (e : W) (v : M.V), I ((e : D.HK.V) ⊗ₜ v) = io (e ⊗ₜ v)) ∧

  (IsGIntw F D.HK M I) ∧

  (∀ I', IsGIntw F D.HK M I' → (∀ (e : W) (v : M.V), I' ((e : D.HK.V) ⊗ₜ v) = io (e ⊗ₜ v)) →
    I' = I) ∧

  (∀ v : M.V, v ≠ 0 →
    Function.Injective (fun x : D.HK.V => I (x ⊗ₜ v)) ∧
    Set.range (fun x : D.HK.V => I (x ⊗ₜ v)) =
      (GlobalTheory.FockAlg.genSub F.act1 (Set.range fun e : W => io (e ⊗ₜ v)) : Set (Pol p q n 0))) ∧

  (∀ (x x' : D.HK.V) (v v' : M.V), inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.ι (I (x ⊗ₜ v))) =
    ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.ι x) * inner ℂ (j v') (j v)) ∧

  (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
    F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧

  (∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
    ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) ∧

  (∀ (g : T1.G) (e e' : W) (v v' : M.V),
    inner ℂ (F.ι (io (e' ⊗ₜ v'))) (F.π (g, 1) (F.ι (io (e ⊗ₜ v)))) =
      ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι e') (D.U.π g (D.ι e)) * inner ℂ (j v') (j v)) ∧

  (∀ (e e' : W) (v : M.V), ‖D.ι e‖ = 1 → ‖D.ι e'‖ = 1 → ‖j v‖ = 1 →
    Integrable (fun g => inner ℂ (F.ι (io (e' ⊗ₜ v))) (F.π (g, 1) (F.ι (io (e ⊗ₜ v)))) *
      star (inner ℂ (D.ι e') (D.U.π g (D.ι e)))) T1.haar ∧
    ∫ g, inner ℂ (F.ι (io (e' ⊗ₜ v))) (F.π (g, 1) (F.ι (io (e ⊗ₜ v)))) *
      star (inner ℂ (D.ι e') (D.U.π g (D.ι e))) ∂T1.haar = ((‖F.ι Δ‖ ^ 2 / D.fdeg : ℝ) : ℂ))

end Maps

def IsCompactType {n : ℕ} {T : GrpData n 0} (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (Λ' : Ix n 0 → ℚ) (v0 : M.V) : Prop :=
  IrrU τ ∧ IsHCMod τ M j ∧ IsHW M.act Λ' v0 ∧ ‖j v0‖ = 1

def HarmonicModule : Prop :=
  ∀ (p q n : ℕ) (hn : p + q < n), 1 ≤ p + q →
  ∀ (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) →
  ∀ (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0)
    (F : FockData T0 T1 T2),
  ∃ (D : DSRep T1) (W : Submodule ℂ D.HK.V),
    IsLowestType D.HK (wtK n ap am) W ∧
    blattner (hcParam n ap am) = wtK n ap am ∧ HasParam D (hcParam n ap am) ∧
    (∀ k₁ ∈ T1.Kset, ∀ k₂ ∈ T1.Kset, ∀ X ∈ pR p q, ∀ e e' : W,
      ‖inner ℂ (D.ι e') (D.U.π (k₁ * T1.expt X * k₂) (D.ι e))‖ ≤ decay n X * ‖D.ι e‖ * ‖D.ι e'‖) ∧
    (∃ e0 : W, (e0 : D.HK.V) ∈ wtSub D.HK.act (wtExt n ap am) ∧ ‖D.ι e0‖ = 1) ∧
    (∃ (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (v0 : M.V), IsCompactType τ M j (wtH n ap am) v0) ∧
    ∀ (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (v0 : M.V), IsCompactType τ M j (wtH n ap am) v0 →
    ∀ e0 : W, (e0 : D.HK.V) ∈ wtSub D.HK.act (wtExt n ap am) → ‖D.ι e0‖ = 1 →
      ∃ (io : W ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0),
        HarmonicMaps F D W τ M j (delta hn ap am) e0 v0 io I

example (a b : ℕ) : delta (p := 1) (q := 1) (n := 3) (by norm_num) (fun _ => a) (fun _ => b) =
    MvPolynomial.X (Sum.inl 0, Sum.inl 0) ^ a * MvPolynomial.X (Sum.inr 0, Sum.inl 2) ^ b := by
  simp [delta, minorProd, nextRow, zPlus, zMinus, topRows, botRows]

example (p q n : ℕ) : decay n (0 : Mat p q) = 1 := by
  have : (0 : Mat p q).toBlocks₁₂ = 0 := rfl
  simp [decay, this]

end GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ToricLatticeDenominators
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

def IsLatIn (V : Submodule (FractionRing R) W) (L : Submodule R W) : Prop :=
  L.FG ∧ Submodule.span (FractionRing R) (L : Set W) = V

def IsIdx (l : ℕ) (V : Submodule (FractionRing R) W) (L₁ L₂ : Submodule R W) (x : ℝ) : Prop :=
  IsLatIn V L₁ ∧ IsLatIn V L₂ ∧
    ∃ g : ↥V ≃ₗ[FractionRing R] ↥V, (∀ v : ↥V, (v : W) ∈ L₁ ↔ ((g v : ↥V) : W) ∈ L₂) ∧
      x = vK R l (LinearMap.det (g : ↥V →ₗ[FractionRing R] ↥V))

theorem vK_one (l : ℕ) : vK R l 1 = 0 := by
  have h := (IsLocalization.surj (nonZeroDivisors R) (1 : FractionRing R)).choose_spec
  rw [one_mul] at h
  have h' := IsFractionRing.injective R (FractionRing R) h
  simp only [vK]
  rw [h', sub_self]

omit [IsScalarTower R (FractionRing R) W] in

theorem isIdx_self (l : ℕ) (V : Submodule (FractionRing R) W) (L : Submodule R W) (h : IsLatIn V L) :
    IsIdx l V L L 0 := by
  refine ⟨h, h, LinearEquiv.refl _ _, fun v => Iff.rfl, ?_⟩
  simp [vK_one]

end Index

section Lattices

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

def eOp : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)) (Y.eAlg i b)

def AOp : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  ((Nat.card (G0g N) : ℕ) : FractionRing (X.O i)) • eOp Y i j b

def typePart : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  ⨅ u : Y.U, Module.End.eigenspace
    ((Y.actG i j b u : Y.Fm i j b ≃ₗ[FractionRing (X.O i)] Y.Fm i j b) :
      Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i))

def V0 : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  LinearMap.range (eOp Y i j b) ⊓ typePart Y i j b

def Theta : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) (Set.range (Y.th i j b))

def ATheta : Submodule (X.O i) (Y.Fm i j b) :=
  (Theta Y i j b).map ((AOp Y i j b).restrictScalars (X.O i))

def IsBasisSeries {n : ℕ} (d : Fin n → Y.Dat i j b) : Prop :=
  IsLatIn (V0 Y i j b) (ATheta Y i j b) ∧
    LinearIndependent (X.O i) (fun a => AOp Y i j b (Y.th i j b (d a))) ∧
    Submodule.span (X.O i) (Set.range fun a => AOp Y i j b (Y.th i j b (d a))) = ATheta Y i j b

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

abbrev FmExt : Type := FractionRing O' ⊗[X.O i] Y.Fm i j b

def eExt : FmExt Y i j b O' →ₗ[O'] FmExt Y i j b O' :=
  (((eOp Y i j b).restrictScalars (X.O i)).baseChange (FractionRing O')).restrictScalars O'

def invariantSpanBaseChange : Submodule (FractionRing O') (FmExt Y i j b O') :=
  Submodule.span (FractionRing O')
    ((fun x => (1 : FractionRing O') ⊗ₜ[X.O i] x) '' (V0 Y i j b : Set (Y.Fm i j b)))

def ThetaExt : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' ((fun x => (1 : FractionRing O') ⊗ₜ[X.O i] x) '' (Theta Y i j b : Set (Y.Fm i j b)))

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def incl : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.O i] FmExt Y i j b O' :=
  LinearMap.rTensor (Y.Fm i j b)
    ((IsScalarTower.toAlgHom (X.O i) O' (FractionRing O')).comp
      (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O')).toLinearMap

def ThetaPsi (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' (⋃ d ∈ {d : Y.Dat i j b | Disjoint (Y.lev i j b d) Q},
    incl Y i j b O' k '' Y.thPsi i j b k Q ψ d)

def ThetaMt (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' ((fun f => incl Y i j b O' k (Y.thP i j b k Q ψ f)) ''
    (Y.MtLat i j b k Q ψ : Set (Y.MtV i j b k Q ψ)))

theorem thetaPsi_one : ThetaPsi Y i j b O' k ∅ 1 = ThetaExt Y i j b O' := by
  have hi : ∀ x : Y.Fm i j b, incl Y i j b O' k ((1 : X.Ok i k) ⊗ₜ[X.O i] x) =
      (1 : FractionRing O') ⊗ₜ[X.O i] x := by
    intro x; simp [incl]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro y hy
    simp only [Set.mem_iUnion, Y.thPsi_one, Set.image_singleton, Set.mem_singleton_iff, hi] at hy
    obtain ⟨d, -, rfl⟩ := hy
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨d, rfl⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      refine Submodule.subset_span ?_
      simp only [Set.mem_iUnion, Y.thPsi_one, Set.image_singleton, Set.mem_singleton_iff, hi]
      exact ⟨d, by simp, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul O' a]
      exact Submodule.smul_mem _ _ hx

end Lattices

section Statement

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def partBAt (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) (ε : ℝ) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']
    [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O'] [Module.Finite (X.Ok i k) O'],
    Function.Injective (algebraMap (X.Ok i k) O') →
    IsLatIn (invariantSpanBaseChange Y i j b O') ((ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O')) ∧
    (ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O') ≤
      (ThetaMt Y i j b O' k Q ψ).map (eExt Y i j b O') ∧
    ∀ M : Submodule O' (FmExt Y i j b O'), IsLatIn (invariantSpanBaseChange Y i j b O') M →
      ∃ x y : ℝ,
        IsIdx (X.l i) (invariantSpanBaseChange Y i j b O') M ((ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O')) x ∧
        IsIdx (X.l i) (invariantSpanBaseChange Y i j b O') M ((ThetaExt Y i j b O').map (eExt Y i j b O')) y ∧
        x ≤ y + ε

def ThroughDel (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : GE N →* (X.Ok i k)ˣ) : Prop :=
  ∃ (M : ℕ) (ψ₀ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    1 ≤ M ∧ ψ = ψ₀.comp (Y.delU i Q M)

variable (bkP : BKPh X)

def exportAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i →
  ∃ (n : ℕ → Bool → ℕ) (d : ∀ j b, Fin (n j b) → bkP.ex.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IsBasisSeries bkP.ex i j b (d j b)) ∧
    ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (epsB : ℕ → Bool → ℝ),
      PsiOk i A Q k' ψ' ∧
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (a : Fin (n j b)), Disjoint (bkP.ex.lev i j b (d j b a)) Q) ∧
      ThroughDel bkP.ex i k' Q (ψ'.comp (X.art i Q)) ∧
      (∀ j b, 0 ≤ epsB j b) ∧ ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
        partA bkP i Q k' (ψ' ^ a) eps' ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
          partBAt bkP.ex i j b k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (epsB j b)) ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps'

theorem projectionDerivative_of_exportAt (N0 : X.Tw → ℕ) (i : X.Tw) (h : exportAt bkP N0 i) : ProjectionDerivativeEstimate bkP N0 i := by
  intro hs eps' he A
  obtain ⟨n, d, -, H⟩ := h hs
  obtain ⟨Q, k', ψ', epsB, h1, -, -, -, -, h2⟩ := H eps' he A
  obtain ⟨ha, hat, -, hc, hd⟩ := h2 1 isCoprime_one_left
  rw [zpow_one] at ha hat hc hd
  exact ⟨Q, k', ψ', h1, ha, hat, hc, hd⟩

end Statement

def aux₃ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → exportAt (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 i

def BoundedDenominatorsCase (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, Formalism.MainNotions.BlochKatoReduction.adm9 D N0 → aux₃ D (Formalism.MainNotions.BlochKatoReduction.bk0 D) N0

end GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

end
end

