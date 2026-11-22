import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import GroundTheory.PAdicHodge.FiniteFlat

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
section
namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def pullFun (R : Type) [CommRing R] (ι : H →* T) : (T → R) →ₐ[R] (H → R) :=
  Pi.algHom R _ fun h => Pi.evalAlgHom R (fun _ : T => R) (ι h)

def resOrder (ι : H →* T) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.map (pullFun R ι)

def quotOrder (π : T →* H) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.comap (pullFun R π)

def muOrder (R : Type) [CommRing R] (T : Type) [CommGroup T] : Subalgebra R (T → R) :=
  Algebra.adjoin R {f | ∃ χ : T →* Rˣ, f = fun t => ((χ t : Rˣ) : R)}

def dualOrder (A : Subalgebra R (T → R)) : Subalgebra R ((T →* Rˣ) → R) :=
  Algebra.adjoin R {g | ∃ l : A →ₗ[R] R, ∀ (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A), g χ = l ⟨_, h⟩}

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IntStable
section
namespace GlobalTheory.CompanionTheory.Ar.HS

open MvPolynomial NumberField GroundTheory.Heights₂.Heights

noncomputable section

section Forms
variable {R : Type*} [CommRing R] {k D N n : ℕ}

def comb (w : Fin n → Fin N → R) (x : Fin n → R) : Fin N → R := fun j => ∑ a, x a * w a j

def pair (u y : Fin N → R) : R := ∑ j, u j * y j

def pull (w : Fin n → Fin N → R) (f : MvPolynomial (Fin k × Fin N) R) :
    MvPolynomial (Fin k × Fin n) R :=
  bind₁ (fun ij => ∑ a, C (w a ij.2) * X (ij.1, a)) f

def pull1 (w : Fin n → Fin N → R) (g : MvPolynomial (Fin N) R) : MvPolynomial (Fin n) R :=
  bind₁ (fun j => ∑ a, C (w a j) * X a) g

def consPt (ξ : Fin N → R) (s : Fin D → Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun ij => Fin.cases (motive := fun _ => R) (ξ ij.2) (fun i => s i ij.2) ij.1

def specRest (f : MvPolynomial (Fin (D + 1) × Fin N) R) (s : Fin D → Fin N → R) :
    MvPolynomial (Fin N) R :=
  bind₁ (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin N) R) (X ij.2)
    (fun i => C (s i ij.2)) ij.1) f

def IsTransv (J : Set (MvPolynomial (Fin N) R)) (s : Fin D → Fin N → R) (y : Fin N → R) : Prop :=
  y ≠ 0 ∧ (∀ g ∈ J, eval y g = 0) ∧ (∀ i, pair (s i) y = 0) ∧
    ∀ v : Fin N → R, (∀ g ∈ J, ∑ j, eval y (pderiv j g) * v j = 0) → (∀ i, pair (s i) v = 0) →
      ∃ c : R, v = c • y

def Splits {δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) R) (θ : Fin N → R)
    (s : Fin D → Fin N → R) (y : Fin δ → Fin N → R) : Prop :=
  (∃ c : R, c ≠ 0 ∧ specRest f s = C c * ∏ q, linForm (y q)) ∧
    (∀ q q', q ≠ q' → ∀ c : R, y q ≠ c • y q') ∧ ∀ q, pair θ (y q) ≠ 0

end Forms

section Heights
variable {K : Type*} [Field K] [NumberField K]

def hfin {ι : Type*} (g : MvPolynomial ι K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)

def meanEmb (a : (K →+* ℂ) → ℝ) : ℝ := (1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, a σ

def chowHtW {k N n : ℕ} (w : Fin n → Fin N → K) (H : ArchData K N) (δ : ℕ)
    (f : MvPolynomial (Fin k × Fin N) K) : ℝ :=
  hfin (pull w f) +
    meanEmb fun σ => mahler (H.normAt σ) k (f.map σ) + k * δ * (harmonic (N - 1) : ℝ) / 2

def ptHt {F : Type*} [Field F] [NumberField F] [Algebra F K] {N n : ℕ} (w : Fin n → Fin N → F)
    (H : ArchData F N) (y : Fin N → K) : ℝ :=
  (1 / Module.finrank ℚ K : ℝ) *
    (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (⨆ a, NumberField.HeightOneSpectrum.adicAbv K v
        (pair (fun j => algebraMap F K (w a j)) y))) +
    meanEmb fun τ : K →+* ℂ =>
      Real.log ((H.normAt (τ.comp (algebraMap F K))).dualNorm fun j => τ (y j))

end Heights

structure ChowData (F : Type) [Field F] [NumberField F] (D N n δ : ℕ) where

  I : Ideal (MvPolynomial (Fin N) F)
  projPrime : IsProjPrime I
  nondeg : ∀ u : Fin N → F, linForm u ∈ I → u = 0
  one_le_D : 1 ≤ D

  f : MvPolynomial (Fin (D + 1) × Fin N) F
  chow : IsChowForm I (D + 1) f
  homog : IsMultiHomog δ f

  w : Fin n → Fin N → F
  span_top : Submodule.span F (Set.range w) = ⊤
  int_stable : ∀ (c : 𝓞 F) (a : Fin n), (c : F) • w a ∈ Submodule.span ℤ (Set.range w)

  H : ArchData F N

  Λ : ℝ
  one_le_Λ : 1 ≤ Λ
  w_le : ∀ (a : Fin n) (σ : F →+* ℂ), (H.normAt σ).norm (fun j => σ (w a j)) ≤ Λ

  θ : Fin N → F
  θ_ne : θ ≠ 0

namespace ChowData
variable {F : Type} [Field F] [NumberField F] {D N n δ : ℕ} (X : ChowData F D N n δ)

def h : ℝ := chowHtW X.w X.H δ X.f / (((D : ℝ) + 1) * δ)

def Theta : ℝ := n * D * δ * (2 + |X.h| + Real.log X.Λ)

def rho0 (l : ℕ) : ℝ := 8 * D * δ * n * l * X.Λ

def eqs {Ω : Type*} [Field Ω] (σ : F →+* Ω) : Set (MvPolynomial (Fin N) Ω) :=
  MvPolynomial.map σ '' (X.I : Set (MvPolynomial (Fin N) F))

variable {K : Type} [Field K] [NumberField K] [Algebra F K]

def sec (x : Fin D → Fin n → 𝓞 K) : Fin D → Fin N → K :=
  fun i => comb (fun a j => algebraMap F K (X.w a j)) fun a => (x i a : K)

def normK (τ : K →+* ℂ) (u : Fin N → K) : ℝ :=
  (X.H.normAt (τ.comp (algebraMap F K))).norm fun j => τ (u j)

def SplitsAt (x : Fin D → Fin n → 𝓞 K) (y : Fin δ → Fin N → K) : Prop :=
  Splits (X.f.map (algebraMap F K)) (fun j => algebraMap F K (X.θ j)) (X.sec x) y

structure ChoiceOut (l : ℕ) (x : Fin D → Fin n → 𝓞 K) (y : Fin δ → Fin N → K) : Prop where
  splits : X.SplitsAt x y
  norm_le : ∀ τ i, X.normK τ (X.sec x i) ≤ X.rho0 l * (1 + 1 / (8 * D * δ))
  norm_ge : ∀ τ i, X.rho0 l * (1 - 1 / (8 * D * δ)) ≤ X.normK τ (X.sec x i)
  ht_ge : ((D : ℝ) + 1) * δ * X.h + D * δ * Real.log (X.rho0 l) -
      δ * (((D : ℝ) + 1) * (harmonic (N - 1) : ℝ) / 2 + Real.log 2 / δ + 1 / 8) ≤
    ∑ q, ptHt X.w X.H (y q)
  ht_le : ∑ q, ptHt X.w X.H (y q) ≤ ((D : ℝ) + 1) * δ * X.h +
      δ * ∑ i, meanEmb fun τ : K →+* ℂ => Real.log (X.normK τ (X.sec x i))
  residue : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P

end ChowData

end

end GlobalTheory.CompanionTheory.Ar.HS
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsGroupHomog
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Short

open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0

variable (F : Type) [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] (D : ℕ) {N : ℕ}

abbrev coefField (x : Fin N → Ω) : IntermediateField F (OmS Ω D N) :=
  IntermediateField.adjoin F (Set.range (sImg (D := D) (0 : Fin (N + 1)) x))

def secDeg (x : Fin N → Ω) : ℕ := Module.finrank (coefField F D x) (OmS Ω D N)

def genForm (x : Fin N → Ω) : OmS Ω D N :=
  ∑ j : Fin (N + 1), sImg (D := D) (0 : Fin (N + 1)) x (0, j) * algebraMap Ω (OmS Ω D N) (Fin.cons (α := fun _ => Ω) 1 x j)

def normForm (x : Fin N → Ω) : OmS Ω D N := (Algebra.norm (coefField F D x) (genForm D x) : coefField F D x)

variable {F D} in

def InS (g : MvPolynomial (TVar D N) F) : Prop := ∀ p ∈ g.vars, p.1 ≠ 0

def IsNormChow (x : Fin N → Ω) (Ch : MvPolynomial (TVar D N) F) : Prop :=
  (∃ a b : MvPolynomial (TVar D N) F, a ≠ 0 ∧ b ≠ 0 ∧ InS a ∧ InS b ∧
    sHom (0 : Fin (N + 1)) x Ch * sHom (0 : Fin (N + 1)) x b = sHom (0 : Fin (N + 1)) x a * normForm F D x) ∧
  ∀ g, InS g → g ∣ Ch → IsUnit g

variable {F D} in

def IsGroupHomog (δ : ℕ) (G : MvPolynomial (TVar D N) F) : Prop :=
  ∀ i : Fin (D + 1), G.IsWeightedHomogeneous (fun p : TVar D N => if p.1 = i then 1 else 0) δ

example (c : F) : InS (C c : MvPolynomial (TVar D N) F) := fun p hp => by simp [vars_C] at hp

end GlobalTheory.CompanionTheory.Ar.Short
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

structure LieLatticeData (Ω F : Type) [Field Ω] (n : ℕ) (Sg : Type) (r s : Sg → ℕ) where

  M : AddSubgroup ((Fin n → F) → Ω)

  lie : ∀ τ, AddSubgroup (Fin (r τ) → Ω)

  W : ∀ τ, AddSubgroup (Fin (r τ) → Ω)

  om : ∀ τ, AddSubgroup (Fin (s τ) → Ω)

  omHT : ∀ τ, AddSubgroup (Fin (s τ) → Ω)

  Gam : ∀ τ, AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω))

  Del : ∀ τ, AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω))

  Th : ∀ τ, AddSubgroup (((Fin n → F) → Ω) × (Fin (r τ) → Ω))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def stdLat (R : Subalgebra o Ω) (ι : Type) : AddSubgroup (ι → Ω) :=
  AddSubgroup.pi Set.univ fun _ => R.toSubring.toAddSubgroup

def divLat {V : Type} [AddCommGroup V] [Module Ω V] (c : Ω) (L : AddSubgroup V) : AddSubgroup V :=
  L.comap (DistribMulAction.toAddMonoidHom V c)

def mulLat {V : Type} [AddCommGroup V] [Module Ω V] (c : Ω) (L : AddSubgroup V) : AddSubgroup V :=
  L.map (DistribMulAction.toAddMonoidHom V c)

def dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) : AddSubgroup (Fin m → Ω) :=
  ⨅ l ∈ L, R.toSubring.toAddSubgroup.comap
    (AddMonoidHom.mk' (fun v : Fin m → Ω => l ⬝ᵥ v) fun a b => dotProduct_add l a b)

def Summand {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (U : Submodule Ω V) : Prop :=
  ∃ ρ : V →ₗ[Ω] V, (∀ v, ρ v ∈ U) ∧ (∀ u ∈ U, ρ u = u) ∧ ∀ v ∈ L, ρ v ∈ L

def powSpan (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) : AddSubgroup Ω :=
  spanOver R ((fun c => c ^ p) '' (X : Set Ω))

variable {F : Type} [Zero F] {n : ℕ}

def linMap (n : ℕ) (χ : F → Ω) : (Fin n → Ω) →ₗ[Ω] ((Fin n → F) → Ω) :=
  Fintype.linearCombination Ω fun (i : Fin n) (x : Fin n → F) => χ (x i)

def vanSub (Ω F : Type) [Field Ω] [Zero F] (n i : ℕ) : Submodule Ω ((Fin n → F) → Ω) :=
  Submodule.pi {x | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} fun _ => ⊥

def charSub (χ : F → Ω) (i : Fin n) : Submodule Ω ((Fin n → F) → Ω) :=
  vanSub Ω F n ((i : ℕ) + 1) ⊔ Submodule.span Ω {fun x => χ (x i)}

def annSub (Ω : Type) [Field Ω] (n i : ℕ) : Submodule Ω (Fin n → Ω) :=
  Submodule.pi {j | (j : ℕ) < i} fun _ => ⊥

def bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) : (ι → Ω) →ₗ[Ω] (ι → C) :=
  (Algebra.linearMap Ω C).compLeft ι

namespace LieLatticeData

variable {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)

def bc {C : Type} [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C) : LieLatticeData C F n Sg r s where
  M := spanOver RC (bcMap Ω C _ '' D.M)
  lie τ := spanOver RC (bcMap Ω C _ '' D.lie τ)
  W τ := spanOver RC (bcMap Ω C _ '' D.W τ)
  om τ := spanOver RC (bcMap Ω C _ '' D.om τ)
  omHT τ := spanOver RC (bcMap Ω C _ '' D.omHT τ)
  Gam τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Gam τ)
  Del τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Del τ)
  Th τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Th τ)

def l1 : AddSubgroup ((Fin n → F) → Ω) := D.M ⊔ mulLat (p : Ω) (stdLat R _)

def af (χ : F → Ω) : AddSubgroup (Fin n → Ω) := (D.l1 R p).comap (linMap n χ).toAddMonoidHom

def hh (χ : F → Ω) : AddSubgroup (Fin n → Ω) := dotDual R (D.af R p χ)

def dId (χ : F → Ω) (i : Fin n) : AddSubgroup Ω :=
  (D.af R p χ ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)

def xId (χ : F → Ω) (i : Fin n) : AddSubgroup Ω :=
  (D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup).comap
    (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun x => χ (x i)).toAddMonoidHom

def kk (τ : Sg) (i : ℕ) : AddSubgroup (Fin (r τ) → Ω) :=
  (D.Th τ ⊓ (vanSub Ω F n i).toAddSubgroup.prod ⊤).map (AddMonoidHom.snd _ _)

def stepGraph (τ : Sg) (χ : F → Ω) (i : Fin n) : AddSubgroup (Ω × (Fin (r τ) → Ω)) :=
  (D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥).comap
    ((LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun x => χ (x i)).toAddMonoidHom.prodMap
      (AddMonoidHom.id _))

def imH (τ : Sg) (χ : F → Ω) : AddSubgroup (Fin (s τ) → Ω) :=
  (D.Del τ ⊓ (D.hh R p χ).prod ⊤).map (AddMonoidHom.snd _ _)

def kerH (τ : Sg) (χ : F → Ω) : AddSubgroup (Fin (r τ) → Ω) :=
  (D.Gam τ ⊓ (⊤ : AddSubgroup _).prod (D.hh R p χ)).map (AddMonoidHom.fst _ _)

variable [Fintype F] (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg)

structure Base : Prop where
  freeM : LocFree R (Fintype.card F ^ n) D.M
  M_le : D.M ≤ stdLat R _
  le_M : ∃ m : ℕ, mulLat ((p : Ω) ^ m) (stdLat R _) ≤ D.M
  one_mem : (1 : (Fin n → F) → Ω) ∈ D.M
  free : ∀ τ, LocFree R (r τ) (D.lie τ) ∧ LocFree R (r τ) (D.W τ) ∧ LocFree R (s τ) (D.om τ) ∧
    LocFree R (s τ) (D.omHT τ)
  incl : ∀ τ, D.lie τ ≤ D.W τ ∧ D.W τ ≤ divLat w (D.lie τ) ∧ D.omHT τ ≤ D.om τ ∧
    D.om τ ≤ divLat w (D.omHT τ)
  stable : ∀ τ, ∀ a ∈ R, (∀ v ∈ D.Gam τ, a • v ∈ D.Gam τ) ∧ (∀ v ∈ D.Del τ, a • v ∈ D.Del τ) ∧
    ∀ v ∈ D.Th τ, a • v ∈ D.Th τ
  gam : ∀ τ, (∀ a, (∃ b, (a, b) ∈ D.Gam τ) ↔ w • a ∈ D.W τ) ∧ (∀ b, (0, b) ∈ D.Gam τ ↔ b ∈ stdLat R _) ∧
    ∀ a, (a, 0) ∈ D.Gam τ ↔ a ∈ D.W τ
  del : ∀ τ, (∀ b, (∃ c, (b, c) ∈ D.Del τ) ↔ w • b ∈ stdLat R _) ∧
    (∀ c, (∃ b, (b, c) ∈ D.Del τ) ↔ w • c ∈ D.omHT τ) ∧ (∀ c, (0, c) ∈ D.Del τ ↔ c ∈ D.omHT τ) ∧
    ∀ b, (b, 0) ∈ D.Del τ ↔ ∃ a, (a, b) ∈ D.Gam τ
  th : ∀ τ, (∀ g, (∃ m, (g, m) ∈ D.Th τ) ↔ g ∈ D.M ∧ g 0 = 0) ∧
    (∀ m, (∃ g, (g, m) ∈ D.Th τ) ↔ m ∈ dotDual R (D.lie τ)) ∧
    ∀ m, (0, m) ∈ D.Th τ ↔ m ∈ mulLat (p : Ω) (dotDual R (D.lie τ))

structure Good₁ : Prop where
  l1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)
  lin : ∀ τ, Summand (D.l1 R p) (LinearMap.range (linMap n (χ τ)))
  van : ∀ i, Summand D.M (vanSub Ω F n i)
  char : ∀ τ i, Summand D.M (charSub (χ τ) i)

structure Good₂ : Prop where
  ann : ∀ τ i, Summand (D.af R p (χ τ)) (annSub Ω n i)
  kk : ∀ τ i, LocFree R (r τ) (D.kk τ i)
  step : ∀ τ i, LocFree R (r τ) ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _))
  im : ∀ τ, LocFree R (s τ) (D.imH R p τ (χ τ))

structure Facts : Prop where
  le_af : ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)
  im : ∀ τ, D.imH R p τ (χ τ) = D.om τ
  ker : ∀ τ, D.kerH R p τ (χ τ) = divLat w (D.lie τ)
  dx : ∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i
  onto : ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i
  inj : ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) =
    powSpan R p (D.xId (χ τ) i)

end LieLatticeData

def IsTestPt (p : ℕ) (R : Subalgebra o Ω) {C : Type} [Field C] [Algebra o C] [Algebra Ω C]
    (RC : Subalgebra o C) : Prop :=
  IsAlgClosed C ∧ (∃ v : Valuation C NNReal, (∀ c, c ∈ RC ↔ v c ≤ 1) ∧ v (p : C) < 1) ∧
    IsAdicComplete (Ideal.span {(p : RC)}) RC ∧ ∀ a ∈ R, algebraMap Ω C a ∈ RC

def LieLatticeData.TestFacts {Sg : Type} {r s : Sg → ℕ} [Fintype F] (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg) : Prop :=
  ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
    IsTestPt p R RC →
      (D.bc RC).Facts RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) φ

def CharData [One F] {Sg : Type} (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω) : Prop :=
  (p : Ω) ≠ 0 ∧ w ∈ R ∧ (∃ c ∈ R, (p : Ω) = c * w) ∧ (0 : F) ≠ 1 ∧
    ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1 ∧ ∀ a, χ τ a ∈ R

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
section
namespace GlobalTheory.CompanionTheory.Ar.BT

open GroundTheory.PAdicHodge

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

noncomputable def secPt (G : FiniteFlatGroupScheme.{0, 0} R) {A : Subalgebra R (T → R)} (e : G.H ≃ₐ[R] A) (t : T) :
    G.Points R :=
  WithConv.toConv ((evalAt A t).comp e.toAlgHom)

def Models (G : FiniteFlatGroupScheme.{0, 0} R) (A : Subalgebra R (T → R)) (e : G.H ≃ₐ[R] A) : Prop :=
  ∀ s t, secPt G e (s * t) = secPt G e s * secPt G e t

end GlobalTheory.CompanionTheory.Ar.BT
end

