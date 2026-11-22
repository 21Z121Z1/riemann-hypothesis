import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0005

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CMUniformizationSpread
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def omegaC (H : Host E) : ℂ := (1 + H.rt0) / 2

def pureSub {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (pos : Bool) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ j, (ty j (H.rt : E) = H.rt0 ↔ pos = false) → P x j = 0}
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  zero_mem' := by
    intro j _
    simp
  smul_mem' := by
    intro a x hx j hj
    rw [hP.1, hx j hj, mul_zero]

def IsCMUnif (H : Host E) {k : Type} [Field k] (κ : k →+* ℂ) (A : Over (Sp k)) [GrpObj A]
    (e : ℂ → (Over.mk (spMap κ) ⟶ A)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ ∃ m n : ℤ, z = m + n * omegaC H) ∧ IsHolTo Set.univ (fun z => (e z).left)

section Alg

variable {k R : Type} [CommRing k] [CommRing R] {X : Scheme.{0}}

abbrev curveOver (A : Over (Sp k)) (a : k →+* R) (y : Sp R ⟶ X) : Over X :=
  Over.mk (pullback.snd A.hom (spMap a) ≫ y)

def img {A : Over (Sp k)} {a : k →+* R} {y : Sp R ⟶ X} {G : Over X} (φ : curveOver A a y ⟶ G)
    {Z : Scheme.{0}} (t : Z ⟶ Sp R) (p : Over.mk (t ≫ spMap a) ⟶ A) : Over.mk (t ≫ y) ⟶ G :=
  (Over.homMk (pullback.lift p.left t (Over.w p)) (pullback.lift_snd_assoc _ _ _ _) : Over.mk (t ≫ y) ⟶ curveOver A a y) ≫ φ

def IsAlgFamily (D : Datum H) (C : Out.PolAV (Sp k)) (t : SAB H X) (a : k →+* R) (y : Sp R ⟶ X) (ρ : R)
    (pos : Bool) (M : Submodule (𝓞 E) D.La) (φ : M → (curveOver C.A a y ⟶ t.G)) : Prop :=
  (∀ (x : M) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (p q : Over.mk (s ≫ spMap a) ⟶ C.A),
      img (φ x) s (p * q) = img (φ x) s p * img (φ x) s q) ∧
  (∀ x x' : M, φ (x + x') = φ x * φ x') ∧
  (∀ (c : 𝓞 E) (x : M), φ (c • x) = φ x ≫ t.act.act c) ∧
  (∀ (x : M) (v : epsR k ⟶ C.A), IsTangent v →
    ∀ vR : Over.mk (spMap (algebraMap R (DualNumber R)) ≫ spMap a) ⟶ C.A,
      vR.left = spMap (Chart.dualMapR a) ≫ v.left →
      (img (φ x) _ vR ≫ t.act.act H.rt).left =
        spMap (epsScaleR (if pos then ρ else -ρ)) ≫ (img (φ x) _ vR).left) ∧
  ∀ x : M, ∃ N : ℕ, 0 < N ∧
    LBIso (lbPow (t.PP.L.pull (φ x).left) N)
      (lbPow (C.L.pull (pullback.fst C.A.hom (spMap a))) (N * (D.EF (H.w0 • (x : D.La)) (x : D.La)).natAbs))

end Alg

def CMSpread : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P), σ (baseKA l).ρ = H.rt0 →
    ∀ (k : Type) [Field k] [NumberField k] [Algebra k ℂ] (C : Out.PolAV (Sp k)), C.g = 1 →
    ∀ e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A), IsCMUnif H (algebraMap k ℂ) C.A e →
    ∃ (R : Subalgebra k ℂ) (σR : KA l →+* R) (y : Sp R ⟶ Xo.X)
      (φ : ∀ pos : Bool, pureSub hP pos → (curveOver C.A (algebraMap k R) y ⟶ Xo.univ.t.G)),
      R.FG ∧ (∀ b, (σR b : ℂ) = σ b) ∧ y ≫ Xo.s = spMap σR ∧
      spMap R.val.toRingHom ≫ y = U.u i P ∧
      ∀ pos : Bool,
        IsAlgFamily (U.Di i) C Xo.univ.t (algebraMap k R) y (σR (baseKA l).ρ) pos (pureSub hP pos) (φ pos) ∧
        (∀ w : C.A ⟶ C.A, (∀ z, e (omegaC H * z) = e z ≫ w) →
          ∀ (x : pureSub hP pos) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (p : Over.mk (s ≫ spMap (algebraMap k R)) ⟶ C.A),
            img (φ pos x) s (p ≫ w) =
              img (φ pos x) s p ≫ Xo.univ.t.act.act (if pos then H.w0 else H.bar H.w0)) ∧
        ∀ (x : pureSub hP pos) (z : ℂ) (p : Sp ℂ ⟶ pullback C.A.hom (spMap (algebraMap k R))),
          p ≫ pullback.fst _ _ = (e z).left → p ≫ pullback.snd _ _ = spMap R.val.toRingHom →
          p ≫ (φ pos x).left = (U.ex i P (z • P (x : (U.Di i).La))).left

example {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (x : pureSub hP true) : P (H.rt • (x : D.La)) = H.rt0 • P x := by
  funext j
  rw [hP.1, Pi.smul_apply, smul_eq_mul]
  by_cases h : ty j (H.rt : E) = H.rt0
  · rw [h]
  · rw [x.2 j (by simp [h]), mul_zero, mul_zero]

example {k R : Type} [CommRing k] [CommRing R] (a : k →+* R) (A : Over (Sp k)) (v : epsR k ⟶ A) :
    ∃ vR : Over.mk (spMap (algebraMap R (DualNumber R)) ≫ spMap a) ⟶ A,
      vR.left = spMap (Chart.dualMapR a) ≫ v.left := by
  refine ⟨Over.homMk (spMap (Chart.dualMapR a) ≫ v.left) ?_, rfl⟩
  have hv : v.left ≫ A.hom = spMap (algebraMap k (DualNumber k)) := Over.w v
  change (spMap (Chart.dualMapR a) ≫ v.left) ≫ A.hom = spMap (algebraMap R (DualNumber R)) ≫ spMap a
  rw [Category.assoc, hv, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext b <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialEtaPeriod
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

def principalForm (Λ : Submodule ℤ ℂ) (z w : ℂ) : ℂ :=
  z * starRingEnd ℂ w / (ZLattice.covolume Λ : ℝ)

def sqLen (Λ : Submodule ℤ ℂ) (z : ℂ) : ℝ := Real.pi * (principalForm Λ z z).re

def IsExponential {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (D : epsR R ⟶ A) (φ : R →+* ℂ)
    (ex : ℂ → (Over.mk (spMap φ) ⟶ A)) (Λ : Submodule ℤ ℂ) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ Λ) ∧
    DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤ ∧
    IsHolTo Set.univ (fun z => (ex z).left) ∧
    IsDerivAt0 (g := 1) (fun z => (ex (z 0)).left) (fun _ => 1)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ D.left)

def IsClassPoint {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) (C : ClassGroup (𝓞 K)) (τ : ℍ) : Prop :=
  ∃ (I : nonZeroDivisors (Ideal (𝓞 K))) (ω : ℂ), ClassGroup.mk0 I = C ∧ ω ≠ 0 ∧
    ∀ z : ℂ, (∃ a ∈ (I : Ideal (𝓞 K)), io (a : K) = z) ↔ ∃ m n : ℤ, z = ω * (m + n * (τ : ℂ))

def etaPeriod (τ : ℍ) : ℝ := 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def HasCMCurveOver {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) (M : Type) [Field M] [NumberField M]
    (s₀ : M →+* ℂ) : Prop :=
  ∃ (j : 𝓞 K →+* 𝓞 M) (A : Over (Sp (𝓞 M))) (_ : GrpObj A) (act : OAct (𝓞 K) A) (D : epsR (𝓞 M) ⟶ A)
    (ex : ∀ s : M →+* ℂ, ℂ → (Over.mk (spMap (s.comp (algebraMap (𝓞 M) M))) ⟶ A))
    (Λ : (M →+* ℂ) → Submodule ℤ ℂ),
    (∀ a : 𝓞 K, s₀ (j a : M) = io (a : K)) ∧
    ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A ∧
    IsLieBasis (fun _ : Fin 1 => D) ∧
    (∀ a : 𝓞 K, (D ≫ act.act a).left = spMap (epsScaleR (j a)) ≫ D.left) ∧
    (∀ s, IsExponential A D (s.comp (algebraMap (𝓞 M) M)) (ex s) (Λ s)) ∧
    (∀ (s : M →+* ℂ) (a : 𝓞 K) (z : ℂ), ex s (s (j a : M) * z) = ex s z ≫ act.act a) ∧
    (∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ, z ∈ Λ s₀ ↔ ∃ a : 𝓞 K, z = c * io (a : K)) ∧
    (∃ τ : ClassGroup (𝓞 K) → ℍ, ∀ C, IsClassPoint io C (τ C)) ∧
    ∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ C, IsClassPoint io C (τ C)) →
      (∑ s : M →+* ℂ, Real.log (sqLen (Λ s) 1)) / (Module.finrank ℚ M : ℝ) =
        -((∑ C, Real.log (etaPeriod (τ C))) / (classNumber K : ℝ))

def HasCMCurve {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : NumberField M) (s₀ : M →+* ℂ), HasCMCurveOver io M s₀

def CMCurveWithPeriod : Prop :=
  ∀ (d : ℕ), d.Prime → d % 16 = 7 → ∀ (K : Type) [Field K] [NumberField K] (rt : K),
    Module.finrank ℚ K = 2 → rt ^ 2 = -(d : K) → ∀ io : K →+* ℂ, HasCMCurve io

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

def weilVal (k : ℕ) (n : ℤ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)

def IsMarking (D D' : Datum H) (l : Level H) (ζ : ℂ) (mk : D.La →ₗ[𝓞 E] D'.La) : Prop :=
  (∀ a : D.La, (∃ y : D'.La, mk a = l.M' • y) ↔ ∃ b : D.La, a = l.M' • b) ∧
  (∀ x : D'.La, ∃ (a : D.La) (y : D'.La), x = mk a + l.M' • y) ∧
  ∃ ζ' : ℂ, IsPrimitiveRoot ζ' l.M' ∧ ζ' ^ (l.M' / l.A) = ζ ∧
    ∀ a b : D.La, weilVal l.M' (D'.EF (mk a) (mk b)) = ζ' ^ D.EF a b

def FixesLevel (D' : Datum H) (l : Level H) (ψ : D'.La ≃ₗ[𝓞 E] D'.La) : Prop :=
  (∀ x y, D'.EF (ψ x) (ψ y) = D'.EF x y) ∧
  (∀ x, ψ x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La)) ∧
  ∀ x, ∃ y : D'.La, ψ x - x = l.A • y

def SamePoint (D' : Datum H) (l : Level H) {g : ℕ} (P P' : D'.La →+ (Fin g → ℂ)) : Prop :=
  ∃ (ψ : D'.La ≃ₗ[𝓞 E] D'.La) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), FixesLevel D' l ψ ∧ ∀ x, P' (ψ x) = T (P x)

def IsSympBasis (D' : Datum H) {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) : Prop :=
  ∀ u v, D'.EF (bas u) (bas v) = omegaStd u v

def perE {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => P (bas (Pi.single (Sum.inl j) 1)) i

def perF {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => P (bas (Pi.single (Sum.inr j) 1)) i

def perTau {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := (perF bas P)⁻¹ * perE bas P

def IsHalf {g : ℕ} (a : Fin g → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1 / 2

end Lattice

section Fibre

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))

abbrev univG : Over Xo.X := Xo.univ.t.G

def IsFibre (D' : Datum H) (mk : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X)
    (ex : (Fin g → ℂ) → (Over.mk y ⟶ univG Xo)) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧
  Function.Surjective ex ∧
  (∀ z, ex z = 1 ↔ ∃ x : D'.La, z = P x) ∧
  (∀ (a : 𝓞 E) z, ex (tyAct ty a z) = ex z ≫ Xo.univ.t.act.act a) ∧
  (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = weilVal k (D'.EF a b) →
    Out.WeilIs (univG Xo) Xo.univ.t.PP.L k (ex ((k : ℂ)⁻¹ • P a)) (ex ((k : ℂ)⁻¹ • P b)) (unitOn c)) ∧
  (∀ a : D.La, toUnit (Over.mk y) ≫ Xo.univ.etaA a = ex ((l.A : ℂ)⁻¹ • P (mk a))) ∧
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    toUnit (Over.mk y) ≫ Xo.univ.eta a = ex ((l.M : ℂ)⁻¹ • P (mk a))

def IsExpDeriv (y : Sp ℂ ⟶ Xo.X) (ex : (Fin g → ℂ) → (Over.mk y ⟶ univG Xo)) : Prop :=
  ∃ d : (Fin g → ℂ) → (epsPt y ⟶ univG Xo),
    (∀ w, IsDerivAlong (X := (univG Xo).left) (fun z => (ex z).left) w (d w).left) ∧
    (∀ w w', d (w + w') = d w * d w') ∧
    (∀ (c : ℂ) w, (d (c • w)).left = spMap (epsScale c) ≫ (d w).left) ∧
    ∀ v : epsPt y ⟶ univG Xo,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ univG Xo).left → ∃! w, d w = v

end Fibre

section Component

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

def HolInFamilies : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B →
    IsHolFamily D' ty B Pf →
      HolOn B (fun b => u (Pf b)) ∧
      HolOn (X := (univG Xo).left) (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => (ex (Pf p.1) p.2).left)

def LiftsLocally : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → HolOnOver Xo.s σ B y →
    ∀ b₀ ∈ B, ∀ P₀ : D'.La →+ (Fin g → ℂ), IsPeriodMap D' ty P₀ → u P₀ = y b₀ →
      ∃ (B' : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))),
        IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolFamily D' ty B' Pf ∧ Pf b₀ = P₀ ∧ ∀ b ∈ B', u (Pf b) = y b

def ThetaInFamilies : Prop :=
  ∀ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La, IsSympBasis D' bas →
    (∀ P, IsPeriodMap D' ty P →
      IsUnit (perF bas P).det ∧ (perTau bas P).IsSymm ∧ ((perTau bas P).map Complex.im).PosDef) ∧
    ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B → IsPreconnected B →
      IsHolFamily D' ty B Pf →
        ∃ a c : Fin g → ℂ, IsHalf a ∧ IsHalf c ∧
          IsThetaFamily Xo.univ.t.PP B (fun b => u (Pf b)) (fun b => ex (Pf b))
            (fun b z => thetaChar (perTau bas (Pf b)) a c ((perF bas (Pf b))⁻¹ *ᵥ z))

def IsPiece (mk : D.La →ₗ[𝓞 E] D'.La) : Prop :=
  D'.p = D.p ∧ D'.q = D.q ∧
  IsMarking D D' l (σ (baseKA l).ζ) mk ∧
  (∀ P, IsPeriodMap D' ty P →
    u P ≫ Xo.s = spMap σ ∧ IsFibre Xo ty D' mk P (u P) (ex P) ∧ IsExpDeriv Xo (u P) (ex P)) ∧
  (∀ P P', IsPeriodMap D' ty P → IsPeriodMap D' ty P' → (u P = u P' ↔ SamePoint D' l P P')) ∧
  HolInFamilies Xo ty D' u ex ∧
  LiftsLocally Xo σ ty D' u ∧
  ThetaInFamilies Xo ty D' u ex

end Component

def UnifAt {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∃ (n : ℕ) (Di : Fin n → Datum H) (mk : ∀ i, D.La →ₗ[𝓞 E] (Di i).La)
    (u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
    (ex : ∀ (i) (P : (Di i).La →+ (Fin g → ℂ)), (Fin g → ℂ) → (Over.mk (u i P) ⟶ univG Xo)),
    (∀ i, IsPiece Xo σ ty (Di i) (u i) (ex i) (mk i)) ∧
    (∀ i j P P', IsPeriodMap (Di i) ty P → IsPeriodMap (Di j) ty P' → u i P = u j P' → i = j) ∧
    ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i P, IsPeriodMap (Di i) ty P ∧ u i P = y

def ComplexUnif {D : Datum H} {l : Level H} (Xo : Moduli D l) : Prop :=
  ∀ σ : KA l →+* ℂ, σ (baseKA l).ρ = H.rt0 →
    ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn D ty → UnifAt Xo σ ty

theorem exists_typeFn (D : Datum H) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn D ty := by
  classical
  let S := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).1, fun τ => ?_⟩
  have e₁ : {i : Fin (Fintype.card S) // (e i).1 = τ} ≃ {s : S // s.1 = τ} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have e₂ : {s : S // s.1 = τ} ≃ Fin (sigMult D τ) := Equiv.sigmaSubtype τ
  rw [Nat.card_congr (e₁.trans e₂)]
  simp

theorem incl_over (l : Level H) : (KA l).val.toRingHom (baseKA l).ρ = H.rt0 := rfl

theorem SamePoint.refl (D' : Datum H) (l : Level H) {g : ℕ} (P : D'.La →+ (Fin g → ℂ)) : SamePoint D' l P P :=
  ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    ⟨fun _ _ => rfl, fun _ => by simp, fun _ => ⟨0, by simp⟩⟩, fun _ => rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
end
end

