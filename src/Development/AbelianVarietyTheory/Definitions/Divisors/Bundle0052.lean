import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CoreFinite
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut

namespace GlobalTheory.HCF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def CentralNil (χ : (List (ℝ → GAd σ J) →₀ ℂ) → ℂ) (N : ℕ) (φ : GAd σ J → ℂ) : Prop :=
  ∀ zs : List (List (ℝ → GAd σ J) →₀ ℂ), zs.length = N → (∀ z ∈ zs, IsCentral σ J z) →
    zs.foldr (fun z f => dop z f - χ z • f) φ = 0

def forms (K U : Subgroup (GAd σ J)) (W : Submodule ℂ (K → ℂ)) (X : Set ((List (ℝ → GAd σ J) →₀ ℂ) → ℂ)) (N : ℕ) :
    Set (GAd σ J → ℂ) :=
  {φ | IsAut σ J K φ ∧ (∀ u ∈ U, u ∈ finPts σ J → ∀ g, φ (g * u) = φ g) ∧
    (∀ g, (fun k : K => φ (g * k)) ∈ W) ∧ ∃ χ ∈ X, CentralNil σ J χ N φ}

end GlobalTheory.HCF

namespace GlobalTheory.HCF

def CoreFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ K : Subgroup (GAd σ J), IsMaxCpt σ J K → ∀ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) →
        ∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W →
          ∀ X : Set ((List (ℝ → GAd σ J) →₀ ℂ) → ℂ), X.Finite → ∀ N : ℕ,
            FiniteDimensional ℂ (Submodule.span ℂ (forms σ J K U W X N))

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def diagHerm {κ : Type} [Fintype κ] [DecidableEq κ] (c : (K →+* ℂ) → κ → ℝ) (hc : ∀ σ p, 0 < c σ p) : HermFam K (κ → K) :=
  ofGram (Pi.basisFun K κ) (fun σ => Matrix.diagonal fun p => (((c σ p)⁻¹ ^ 2 : ℝ) : ℂ))
    fun σ => Matrix.PosDef.diagonal fun p => Complex.zero_lt_real.2 (pow_pos (inv_pos.2 (hc σ p)) 2)

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

def prodLat {n δ : ℕ} (j : ℕ) (w : Fin n → Fin δ → K) (Λ : Submodule (𝓞 K) (Fin δ → K)) : Submodule (𝓞 K) (Fin δ → K) :=
  Submodule.span (𝓞 K) {g | ∃ e : Fin j → Fin n, ∃ l ∈ Λ, g = (∏ t, w (e t)) * l}

end Lattice

def HermObject : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (nm : HermFam K V), nm.IsConjInv →
    ∀ (D T n δ : ℕ) (M : Submodule (𝓞 K) V) (U : ℕ → Submodule K V)
      (φ : ∀ a, U a →ₗ[K] (MonoDeg (Fin D) a × Fin δ → K))
      (w : Fin n → Fin δ → K) (Λ : Submodule (𝓞 K) (Fin δ → K))
      (c₁ c₂ : (K →+* ℂ) → Fin δ → ℝ) (r : (K →+* ℂ) → Fin D → ℝ) (h J g β lρ₁ lρ lΛD lΛT C : ℝ)
      (h₂ : ∀ σ p, 0 < c₂ σ p),
      1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 0 ≤ g → 1 ≤ β → 0 ≤ lΛD → 0 ≤ lΛT → 4 ≤ C →
      0 ≤ lρ₁ → lρ₁ ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ → IsFull M → IsFull Λ →
      (∀ σ p, 0 < c₁ σ p) → (∀ σ i, 0 < r σ i) →
      (∀ σ p, c₁ ((starRingEnd ℂ).comp σ) p = c₁ σ p) → (∀ σ p, c₂ ((starRingEnd ℂ).comp σ) p = c₂ σ p) →
      (∀ σ i, r ((starRingEnd ℂ).comp σ) i = r σ i) →
      (∀ p, ∃ k, w k p ≠ 0) → (∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → δ < Ideal.absNorm P) →
      (∀ σ i, r σ i ≤ Real.exp lρ₁) →
      ((D : ℝ) + 1) * h + (∑ i, meanLog K fun σ => r σ i) - g ≤ (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) / δ →
      (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) / δ ≤ ((D : ℝ) + 1) * h + (∑ i, meanLog K fun σ => r σ i) →
      -((δ : ℝ) * J) - ((D : ℝ) + 3) * (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) ≤ deg (diagHerm c₂ h₂) Λ →
      (∀ a < T - D, U (a + 1) ≤ U a ∧ ∀ x : U a, φ a x = 0 ↔ x.1 ∈ U (a + 1)) →
      (∀ a < T - D, ∀ α : MonoDeg (Fin D) a, ∀ γ ∈ prodLat (T - a) w Λ, ∃ f : U a, f.1 ∈ M ∧
        ∀ α' p, φ a f (α', p) = if α'.1 = α.1 then γ p else 0) →
      (∀ a < T - D, ∀ σ, ∀ x : U a, ∀ ε : ℝ, 0 < ε → ∃ y : U a, φ a y = 0 ∧
        nm.nrm σ (x.1 - y.1) ≤
          Real.sqrt (β ^ (T + D + 1) * (34 * cD D) * ((a + D - 1).choose (D - 1) : ℝ) * (∑ i, r σ i ^ 2) ^ D) *
            Real.sqrt (∑ α : MonoDeg (Fin D) a, (∏ i, r σ i ^ α.1 i) ^ 2 *
              ∑ p, ‖σ (φ a x (α, p))‖ ^ 2 / (c₂ σ p * c₁ σ p ^ (T - a)) ^ 2) + ε) →
      (∃ S : Set V, S ⊆ (M : Set V) ∧ S ⊆ (U (T - D) : Set V) ∧
        (∀ x ∈ S, ∀ σ, nm.nrm σ x ≤ Real.exp (((T : ℝ) - D) * (Real.log β / 2 + lρ₁) + lΛD)) ∧
        U (T - D) ≤ Submodule.span K S) →
      (∃ S : Set V, S ⊆ (M : Set V) ∧ (∀ x ∈ S, ∀ σ, nm.nrm σ x ≤ Real.exp lΛT) ∧ Submodule.span K S = ⊤) →
      0 < Module.finrank K V ∧ 0 ≤ 1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ) ∧
      (1 - (1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ))) *
          ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - C * (D : ℝ) ^ 2 * (lρ + Real.log T)
            - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2))
        - (1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ)) *
          ((T : ℝ) * (Real.log 2 + lρ + Real.log β / 2) + lΛD + lΛT)
        ≤ deg nm M / (Module.finrank K V : ℝ)

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)

def resCo {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) : Submodule (𝓞 K) (Fin δ → K) :=
  (X.resLat hs).map ((Co.ev 0).toLinearMap.restrictScalars (𝓞 K))

variable (X) in

structure Stable : Prop where
  nef : IsNef K X.LA
  big : IsBig K X.LA
  mulStable : X.MulStable
  mulBound : ∀ σ, X.MulBoundAt σ X.beta
  integralBound : X.IntegralBound (fun _ => X.beta) fun _ => 1
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

example {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) : RegSeq hL F [] := trivial

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def wtSize (lam : (E →+* ℂ) → DomWeight a) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ k : Fin a, ((lam τ).w k).natAbs

def IntMat (u : HeightOneSpectrum (𝓞 E)) (x : Matrix (Fin a) (Fin a) (u.adicCompletion E)) : Prop :=
  ∀ i j, x i j ∈ u.adicCompletionIntegers E

def IsIntegralOpW (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (w₀ : HeightOneSpectrum (𝓞 E))
    (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    ∃ d : ℕ, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E)))) ∧
      ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

def HasTypeVec (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E)))
    {A : Type} [Group A] (θ : J →* A) (χ : A →* ℂˣ) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x ∈ K, RU E a x φ = φ) ∧
    ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def CongTy : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ), (∀ j, IsIntegralOpW ι lam w₀ (t j)) → ActsBy K t η →
    ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ U, OfType lam K U → HasTypeVec w₀ K J θ 1 U →
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ U', OfType lam K U' ∧ (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
          HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

structure MatchSat (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop where
  off : MatchOffT U π T
  sat : ∀ (w : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt w → w ∉ T →
    ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt U w s ϖ q α → (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam a α)

def BCBackSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ a : ℕ, 1 ≤ a → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
    ∀ w₀, IsSplitAt w₀ → ScU U w₀ →
    ∃ π : CuspSub E a, MatchSat U π T ∧ GlobalTheory.ContraPair.PolarizedPair π (quadChar E ^ a) ∧
      ∀ w, ¬ IsSplitAt w → w ∉ T → ∃ B, (CG.mk π).HasSat w B

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

def fixVar {K ι : Type} [CommRing K] [DecidableEq ι] (r : ι) (c : K) (g : MvPolynomial ι K) : MvPolynomial ι K :=
  aeval (fun j => if j = r then C c else X j) g

def fixBelow {K κ : Type} [CommRing K] {m : ℕ} (r : ℕ) (c : Fin m → K) (g : MvPolynomial (Fin m ⊕ κ) K) :
    MvPolynomial (Fin m ⊕ κ) K :=
  aeval (Sum.elim (fun i : Fin m => if (i : ℕ) < r then C (c i) else X (Sum.inl i)) fun k => X (Sum.inr k)) g

def fixRight {K κ : Type} [CommRing K] {m : ℕ} (e : κ → K) (g : MvPolynomial (Fin m ⊕ κ) K) : MvPolynomial (Fin m ⊕ κ) K :=
  aeval (Sum.elim (fun i => X (Sum.inl i)) fun k => C (e k)) g

def ShearInv {F : Type} [CommRing F] {D N : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  ∀ (i : Fin D) (t : F), aeval (fun p : Fin (D + 1) × Fin N =>
    if p.1 = i.castSucc then X p + C t * X (Fin.last D, p.2) else (X p : MvPolynomial (Fin (D + 1) × Fin N) F)) f = f

def LastNonzero {F : Type} [CommRing F] {D N : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  ∀ u : Fin N → F, u ≠ 0 → ∃ v : Fin D → Fin N → F, eval (join v u) f ≠ 0

structure IsMaxPt {B N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (δ : ℕ) (h : MvPolynomial (Fin B × Fin N) ℂ)
    (p : Fin B × Fin N → ℂ) : Prop where
  unit : ∀ i, frameNorm A (fun j => p (i, j)) = 1
  ne : eval p h ≠ 0
  le : ∀ u : Fin B × Fin N → ℂ, ‖eval u h‖ ≤ ‖eval p h‖ * ∏ i, frameNorm A (fun j => u (i, j)) ^ δ

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def vecs {F E : Type} [Field F] [Field E] [Algebra F E] {D N n : ℕ} (w : Matrix (Fin N) (Fin n) F) (x : Fin D → Fin n → 𝓞 E) :
    Fin D → Fin N → E := fun i => (w.map (algebraMap F E)).mulVec fun k => (x i k : E)

def specHeight {F : Type} [Field F] [NumberField F] {D N n : ℕ} (δ : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (E : Type) [Field E] [NumberField E]
    [Algebra F E] (s : Fin D → Fin N → E) : ℝ :=
  formHeight δ (w.map (algebraMap F E)) (fun τ => A (τ.comp (algebraMap F E))) (spec s f)

def defect {F : Type} [Field F] [NumberField F] {D N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin D → Fin N → E) : ℝ :=
  finPart (linSubst w f) - finPart (linSubst (w.map (algebraMap F E)) (spec s f))

def Core : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (D N n δ : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ h Θ : ℝ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (Q : MvPolynomial (Fin D × Fin N) F),
    1 ≤ D → 1 ≤ δ → ShortLat w A Λ → IsMultiHomogeneous (fun _ => δ) f → ShearInv f → LastNonzero f →
    ((D : ℝ) + 1) * δ * h = formHeight δ w A f → (n : ℝ) * D * δ * (2 + |h| + Real.log Λ) ≤ Θ →
    Q ≠ 0 → (Q.totalDegree : ℝ) ≤ Θ ^ 3 →
    ∃ (l : ℕ) (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (x : Fin D → Fin n → 𝓞 E),
      Θ ^ 20 < l ∧ (l : ℝ) ≤ 2 * Θ ^ 20 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P) ∧
      aeval (fun p : Fin D × Fin N => vecs w x p.1 p.2) Q ≠ 0 ∧ spec (vecs w x) f ≠ 0 ∧
      (∀ i (τ : E →+* ℂ), frameNorm (A (τ.comp (algebraMap F E))) (fun j => τ (vecs w x i j)) ≤
        8 * D * δ * n * l * Λ * (1 + 1 / (8 * D * δ))) ∧
      ((D : ℝ) + 1) * δ * h + D * δ * Real.log (8 * D * δ * n * l * Λ) -
        δ * (((D : ℝ) + 1) * (harmonic (N - 1) : ℝ) / 2 + Real.log 2 / δ + 1 / 8) ≤ specHeight δ w A f E (vecs w x) ∧
      specHeight δ w A f E (vecs w x) ≤ ((D : ℝ) + 1) * δ * h + δ * ∑ i, mean E fun τ =>
        Real.log (frameNorm (A (τ.comp (algebraMap F E))) fun j => τ (vecs w x i j))

def AvoidPoly {F : Type} [Field F] [NumberField F] (T : Tuple F) (e : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧ Q.totalDegree ≤ e ∧
    ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin T.D → Fin T.N → K),
      aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 →
      ∀ x : T.Pt K, (∀ i, ∑ j, s i j * T.coords x.1 j = 0) → ptOf x.1 ∈ nonzeroLocus T.th

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

example : ShortLat (1 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 1) 1 :=
  ⟨one_pos, (projTuple.spans 0), (projTuple.shortGenerators 0).int, fun _ => by simp, fun σ x => by simp [frameNorm],
    fun k σ => (projTuple.shortGenerators 0).le k σ, le_rfl⟩

namespace Check

def det2 (R : Type) [CommRing R] : MvPolynomial (Fin 2 × Fin 2) R := X (0,0) * X (1,1) - X (0,1) * X (1,0)

theorem shortLat_std (M : ℕ) : ShortLat (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ) (fun _ => 1) 1 :=
  ⟨Nat.succ_pos _, projTuple.spans M, (projTuple.shortGenerators M).int, fun _ => by simp,
    fun σ x => by simp [frameNorm], fun k σ => (projTuple.shortGenerators M).le k σ, le_rfl⟩

theorem sl2 : ShortLat (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) 1 := shortLat_std 1

theorem shear2 : ShearInv (D := 1) (det2 ℚ) := by
  intro i t
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [det2, show Fin.last 1 = 1 from rfl]
  ring

theorem join_eval {R : Type} [CommRing R] (v : Fin 1 → Fin 2 → R) (u : Fin 2 → R) :
    eval (join v u) (det2 R) = v 0 0 * u 1 - v 0 1 * u 0 := by
  simp only [det2, map_sub, map_mul, eval_X]
  rfl

theorem last2 : LastNonzero (D := 1) (det2 ℚ) := by
  intro u hu
  refine ⟨fun _ => ![u 1, -u 0], ?_⟩
  rw [join_eval]
  intro h
  simp at h
  apply hu
  funext j
  fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1)]

theorem max2 : IsMaxPt (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 (det2 ℂ) (fun p => if p.1 = p.2 then 1 else 0) := by
  refine ⟨fun i => ?_, by simp [det2], fun u => ?_⟩
  · fin_cases i <;> simp [frameNorm, Fin.sum_univ_two]
  · simp only [det2, frameNorm, Fin.prod_univ_two, Fin.sum_univ_two, map_sub, map_mul, eval_X, inv_one, Matrix.one_mulVec, pow_one]
    simp
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have h := norm_sub_le (u (0,0) * u (1,1)) (u (0,1) * u (1,0))
    rw [norm_mul, norm_mul] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖u (0,0)‖ * ‖u (1,0)‖ - ‖u (0,1)‖ * ‖u (1,1)‖)]

theorem mh2 : IsMultiHomogeneous (fun _ => 1) (det2 ℚ) := by
  have := (GlobalTheory.ChowHt.Model.isChowForm_line ℚ).homog
  rwa [Matrix.det_fin_two] at this

theorem core_hyp : ∃ h Θ : ℝ, ShortLat (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) 1 ∧ IsMultiHomogeneous (fun _ => 1) (det2 ℚ) ∧
    ShearInv (D := 1) (det2 ℚ) ∧ LastNonzero (D := 1) (det2 ℚ) ∧
    (((1 : ℕ) : ℝ) + 1) * (1 : ℕ) * h = formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) ∧
    ((2 : ℕ) : ℝ) * (1 : ℕ) * (1 : ℕ) * (2 + |h| + Real.log 1) ≤ Θ ∧
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 2) ℚ) ≠ 0 ∧
    (((X (0, 0) : MvPolynomial (Fin 1 × Fin 2) ℚ).totalDegree : ℕ) : ℝ) ≤ Θ ^ 3 := by
  refine ⟨formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) / 2, _, sl2, mh2, shear2, last2, by push_cast; ring, le_rfl,
    X_ne_zero _, ?_⟩
  rw [totalDegree_X]
  push_cast
  apply one_le_pow₀
  simp
  linarith [abs_nonneg (formHeight 1 (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 1) (det2 ℚ) / 2)]

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

theorem lin_hom {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => by simpa using (isHomogeneous_X K ((0 : Fin 1), j)).mul (isHomogeneous_C _ (y j))

theorem nosq {K : Type} [Field K] {N : ℕ} {z : Fin N → K} (hz : z ≠ 0) : NoSquare (lin z) := by
  refine ⟨lin_ne hz, fun y hy h => ?_⟩
  have := totalDegree_le_of_dvd_of_isDomain h (lin_ne hz)
  rw [(lin_hom z).totalDegree (lin_ne hz), ((lin_hom y).pow 2).totalDegree (pow_ne_zero _ (lin_ne hy))] at this
  omega

theorem not_nosq {K : Type} [Field K] {N : ℕ} {z : Fin N → K} (hz : z ≠ 0) : ¬ NoSquare (lin z ^ 2) :=
  fun h => h.2 z hz dvd_rfl

theorem avoid : AvoidPoly (projTuple 1) 1 := by
  refine ⟨X ((0 : Fin 1), (0 : Fin 2)), X_ne_zero _, (totalDegree_X _).le, fun K _ _ _ s hs x hx => ?_⟩
  have hb := (projTuple.isAdelic 1 le_rfl).geom.alg.bpf.coords_ne_zero x.1
  have hl : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (projTuple 1).th = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus ((projTuple 1).b (1 : Fin 2)) :=
    GlobalTheory.nonzeroLocus_secToPow _ le_rfl
  rw [hl, ← LinSys.val_ne_zero_iff]
  intro h1
  have h := hx (0 : Fin 1)
  have e : ∑ j, s (0 : Fin 1) j * (projTuple 1).coords x.1 j = s (0 : Fin 1) (0 : Fin 2) * (projTuple 1).coords x.1 (0 : Fin 2) + s (0 : Fin 1) (1 : Fin 2) * (projTuple 1).coords x.1 (1 : Fin 2) := Fin.sum_univ_two _
  have h1' : (projTuple 1).coords x.1 (1 : Fin 2) = 0 := h1
  rw [e, h1', mul_zero, add_zero] at h
  have hs' : s (0 : Fin 1) (0 : Fin 2) ≠ 0 := by simpa using hs
  apply hb
  funext j
  have h0 := (mul_eq_zero.1 h).resolve_left hs'
  revert j
  exact Fin.forall_fin_two.2 ⟨h0, h1'⟩

end Check

end GlobalTheory.HSChoice
end
end

