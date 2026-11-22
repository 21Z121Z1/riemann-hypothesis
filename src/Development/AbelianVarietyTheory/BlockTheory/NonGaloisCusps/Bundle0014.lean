import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Polynomial

section Base

variable {Γ : Type} [Group Γ] {X : Type} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}

abbrev mat {B : Type} [CommRing B] {k : ℕ} (σ : Γ →* GL (Fin k) B) (g : Γ) : Matrix (Fin k) (Fin k) B :=
  ((σ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)

abbrev toFr (A : Type) [CommRing A] : A →+* FractionRing A := algebraMap A (FractionRing A)

def overK {k : ℕ} (σ : Γ →* GL (Fin k) A) : Representation (FractionRing A) Γ (Fin k → FractionRing A) :=
  matRep (mapM (toFr A) ((Units.coeHom _).comp σ))

def InRing (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (a : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (f : Fin m → X → A) (h : Fin m → Γ), (∀ k, f k ∈ T) ∧
    a = ∑ k, fun x => f k x • mat (rep x) (h k)

def InMatrixCongruenceModule (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (e s : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (j : Fin m → X → A) (a : Fin m → X → Matrix (Fin n) (Fin n) A),
    (∀ k, j k ∈ T ∧ j k π = 0 ∧ InRing T rep (a k)) ∧
    s = ∑ k, fun x => j k x • (e x * a k x * e x)

def CharPolyIn (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (h : Γ) (d : ℕ), (fun x => (mat (rep x) h).charpolyRev.coeff d) ∈ T

def ResidualSame (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (x y : X) (h : Γ), ((mat (rep x) h).map (IsLocalRing.residue A)).charpoly =
    ((mat (rep y) h).map (IsLocalRing.residue A)).charpoly

def IsDecomp (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))) :
    Prop :=
  ∀ g u, e (overK σ g u) =
    (overK ρ g (e u).1, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A) * (e u).2 c)

def HidaSetting (t : ℕ) (T : Subalgebra A (X → A)) (Z : Finset X) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) : Prop :=
  IsLocalRing T ∧ (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) ∧
  (∀ x, IsSS (overK (rep x))) ∧
  CharPolyIn T rep ∧
  (∀ x, AbsIrrDistinct (overK (rep x))) ∧ ResidualSame rep ∧
  (∀ x ∈ Z, ∃ e, IsDecomp (t := t) (rep x) (ρ x) χ e) ∧
  (∀ x ∈ Z, AbsIrrSub (mapRep (IsLocalRing.residue A) (ρ x)) ⊤)

def blockPol (e M : Matrix (Fin n) (Fin n) A) : A[X] :=
  Matrix.det ((Polynomial.X : A[X]) • e.map (C (R := A)) - M.map (C (R := A)) + 1 - e.map (C (R := A)))

def IsChoice (t : ℕ) (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) (π : X) (g0 : Γ) (L : ℕ)
    (eB e1 X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧
  (∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
    (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
    ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧
      ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0)) ∧
  (∃ (ϖ : A) (s : X → Matrix (Fin n) (Fin n) A), Irreducible ϖ ∧ InMatrixCongruenceModule T rep π eB s ∧
    X0 = fun x => eB x * mat (rep x) g0 * eB x + ϖ ^ L • s x) ∧
  ∀ x, (((blockPol (eB x) (X0 x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t

def RootsIn (t : ℕ) (B : Type) [CommRing B] [Algebra A B] (eB X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ x, ∃ α : Fin t → FractionRing B,
    (blockPol (eB x) (X0 x)).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - C (α c))

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def IsInertiaCyclotomicGeneratorElement (g0 : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def IsEnlargement (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [Algebra A (N.O i)] (TA : Subalgebra A (N.X i → A))
    (repA : N.X i → (GE N →* GL (Fin R.nV) A)) (ρA : N.X i → (GE N →* GL (Fin R.r) A))
    (χA : ℕ → (GE N →* Aˣ)) : Prop :=
  Function.Injective (algebraMap A (N.O i)) ∧
  Subalgebra.toSubmodule (N.T i) =
    Submodule.span (N.O i) ((fun f : N.X i → A => fun x => algebraMap A (N.O i) (f x)) '' (TA : Set _)) ∧
  (∀ x, rep x = mapRep (algebraMap A (N.O i)) (repA x)) ∧
  (∀ x ∈ N.Z i, ρ x = mapRep (algebraMap A (N.O i)) (ρA x)) ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g, ((N.chi i c g : (N.O i)ˣ) : N.O i) = algebraMap A (N.O i) ((χA c g : Aˣ) : A)

def RepCont (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x, Continuous fun g => mat (rep x) g

def ConsExist : Prop :=
  ∀ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℤ_[N.l i] A]
    [Module.Finite ℤ_[N.l i] A] [Algebra A (N.O i)] [IsScalarTower ℤ_[N.l i] A (N.O i)]
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    RepCont N i rep → IsEnlargement N i rep ρ A TA repA ρA χA → HidaSetting R.t TA (N.Z i) repA ρA χA →
    (∀ π ∈ N.Z i, ∀ g0, IsInertiaCyclotomicGeneratorElement N i g0 → ∀ L : ℕ,
      ∃ eB e1 X0, IsChoice R.t TA repA ρA χA π g0 L eB e1 X0) ∧
    (∀ (g0 : N.X i → GE N) (L : N.X i → ℕ)
        (eB e1 X0 : N.X i → N.X i → Matrix (Fin R.nV) (Fin R.nV) A),
      (∀ π ∈ N.Z i, IsInertiaCyclotomicGeneratorElement N i (g0 π) ∧ IsChoice R.t TA repA ρA χA π (g0 π) (L π) (eB π) (e1 π) (X0 π)) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B),
        Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧
        ∀ π ∈ N.Z i, RootsIn R.t B (eB π) (X0 π)) ∧
    (∀ π ∈ N.Z i, ∀ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 → IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 →
      RootsIn R.t (N.O i) eB X0 →
      ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧
        (∀ x, S.eB x = (eB x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.e1 x = (e1 x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.X0 x = (X0 x).map (algebraMap A (N.O i))) ∧
        GoodCongruenceObjects N rep ρ π S)

def TakenAfter (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra ℤ_[N.l i] A)
    (_ : Module.Finite ℤ_[N.l i] A) (_ : Algebra A (N.O i)) (_ : IsScalarTower ℤ_[N.l i] A (N.O i))
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    IsEnlargement N i rep ρ A TA repA ρA χA ∧ HidaSetting R.t TA (N.Z i) repA ρA χA ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 ∧ IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 ∧
      RootsIn R.t (N.O i) eB X0

theorem isEnlargement_self (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) :
    IsEnlargement N i rep ρ (N.O i) (N.T i) rep ρ (N.chi i) := by
  refine ⟨fun _ _ h => h, ?_, fun x => ?_, fun x _ => ?_, fun _ _ _ _ => rfl⟩
  · have : ((fun f : N.X i → N.O i => fun x => algebraMap (N.O i) (N.O i) (f x)) '' (N.T i : Set _)) =
        (Subalgebra.toSubmodule (N.T i) : Set _) := by
      simp
    rw [this, Submodule.span_eq]
  · ext g a b
    rfl
  · ext g a b
    rfl

end Record

example {A : Type} [CommRing A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) : blockPol 1 M = M.charpoly := by
  unfold blockPol Matrix.charpoly Matrix.charmatrix
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

def ConsExist_at (D : D7) : Prop := ∀ i : D.nd.Loc, ConsExist D.nd i

def ConsExistF {eps : ℝ} (Fm : FamP eps) : Prop := ∀ (x : ℝ) (k : Fm.Ix x), ConsExist_at (Fm.D x k)

def ConsExistClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => ConsExistF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Exceptional

variable {D : D7} (L : SizeData₂ D)

def sigmaPlus : ℤ := ⌊2 * L.sc.b / LevelStarExponents.lStar L⌋

def baseSizes : Set ℝ :=
  {W | W = L.sc.b ∨ W = L.sc.w'' D.R.n ∨
    ∃ τ : D.host.TT, W = (L.bT τ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)}

def window (W₀ : ℝ) : Set ℤ :=
  {n | W₀ + (-L.etaSz - 2 * (sigmaPlus L : ℝ) - 3) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ W₀ + (L.Sc + L.etaSz + L.etaSz + 2 * (sigmaPlus L : ℝ) + 4)}

def excPrimes : Set ℕ :=
  {l | l.Prime ∧ LevelStarExponents.lStar L < (l : ℝ) ∧ ∃ W₀ ∈ baseSizes L, ∃ n ∈ window L W₀, (l : ℤ) ∣ n}

end Exceptional

section Terms

variable (D : D7) (i : D.nd.Loc)

def ramLen : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def ccLen (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)

def selLen (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℕ∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def twistLen : ℕ∞ :=
  (D.R.t : ℕ∞) * ∑ P ∈ D.nd.Q i,
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {zetaP D i P - 1})

def IsBlockSplit (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) :
    Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ φ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, φ ((((r g : GL (Fin D.R.nV) (D.nd.O i)) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)).mulVec u) =
      ((((ρ g : GL (Fin D.R.r) (D.nd.O i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (toK D.nd i)).mulVec (φ u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (φ u).2 c)

end Terms

def LargePrimeBound_at (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc,
    LevelStarExponents.lStar L < (D.nd.l i : ℝ) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    D.nd.l i ∉ excPrimes L →
    HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), IsBlockSplit D i (r π) ρ →
      ccLen D i π ≤ selLen D i ρ π + ramLen D i * shaSum D i +
        ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + twistLen D i

def LargePrimeBoundF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LargePrimeBound_at (Fm.D x i) (Fm.L x i)

def LargePrimeBound (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => LargePrimeBoundF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Rep

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

def IsSemisimplificationOf {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) : Prop :=
  IsSS s ∧ ∃ (m : ℕ) (Ws : Fin m → Submodule k W) (e : W ≃ₗ[k] V),
    (∀ j, Stable s (Ws j)) ∧ DirectSum.IsInternal Ws ∧
    ∀ j g, ∀ v ∈ Ws j, ρ g (e v) - e (s g v) ∈ (⨆ j' ∈ Set.Iio j, Ws j').map (e : W →ₗ[k] V)

def IsIrred {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k Γ V) : Prop :=
  (⊤ : Submodule k V) ≠ ⊥ ∧ ∀ U : Submodule k V, Stable ρ U → U = ⊥ ∨ U = ⊤

def blockSum {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) :
    Representation k Γ ((Fin r → k) × (Fin t → k)) where
  toFun g := LinearMap.prodMap (matRep ρ g)
    (LinearMap.pi fun c => ((χ c g : kˣ) : k) • (LinearMap.proj c : (Fin t → k) →ₗ[k] k))
  map_one' := by
    refine LinearMap.ext fun u => Prod.ext ?_ (funext fun c => ?_) <;> simp
  map_mul' g h := by
    refine LinearMap.ext fun u => Prod.ext ?_ (funext fun c => ?_) <;> simp [mul_assoc]

theorem blockSum_apply {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) (g : Γ)
    (u : (Fin r → k) × (Fin t → k)) :
    blockSum ρ χ g u = ((ρ g).mulVec u.1, fun c => ((χ c g : kˣ) : k) * u.2 c) := by
  refine Prod.ext ?_ (funext fun c => ?_)
  · rfl
  · rfl

theorem isSemisimplificationOf_self {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k Γ V)
    (h : IsSS ρ) : IsSemisimplificationOf ρ ρ := by
  refine ⟨h, 1, fun _ => ⊤, LinearEquiv.refl k V, fun _ _ _ _ => trivial, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨iSupIndep_subsingleton _, by simp⟩
  · intro j g v _
    simp

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

abbrev RepFam : Type := D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))

def matAlong {a : ℕ} {L : Type} [Field L] (f : D.nd.O i →+* L) (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) :
    GE D.nd →* Matrix (Fin a) (Fin a) L :=
  mapM f ((Units.coeHom _).comp ρ)

def chiAlong {L : Type} [Field L] (f : D.nd.O i →+* L) (c : Fin D.R.t) : GE D.nd →* Lˣ :=
  (Units.map f.toMonoidHom).comp (D.nd.chi i ((c : ℕ) + 1))

def redK {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) :
    Representation (kk D.nd i) (GE D.nd) (Fin a → kk D.nd i) :=
  matRep (matAlong D i (IsLocalRing.residue (D.nd.O i)) ρ)

theorem repK_eq (r : RepFam D i) (x : D.nd.X i) :
    repK D.nd i r x = matRep (matAlong D i (toK D.nd i) (r x)) := rfl

def Realised : Prop := ∃ r : RepFam D i, GoodR D.nd i r

def ConstituentsAbsIrrDistinct : Prop :=
  ∀ r : RepFam D i, GoodR D.nd i r → ∀ x, AbsIrrDistinct (repK D.nd i r x)

def ResidualCommon : Prop :=
  ∃ s : Representation (kk D.nd i) (GE D.nd) (Fin D.R.nV → kk D.nd i),
    ∀ r : RepFam D i, GoodR D.nd i r → ∀ x, IsSemisimplificationOf s (redK D i (r x))

def ConstituentsAt : Prop := Realised D i ∧ ConstituentsAbsIrrDistinct D i ∧ ResidualCommon D i

def GoodRowPoint (x₀ : D.nd.X i) : Prop :=
  ∃ (σ : D.what₂.FT) (P : D.naut.AV i),
    D.nd.goodRow σ ∧ thetaOf D.nd D.naut i σ P ∧ D.naut.ptV i P = some x₀

def OffBlock (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e (matRep (matAlong D i (toK D.nd i) r₀) g u) =
      blockSum (matAlong D i (toK D.nd i) ρ) (chiAlong D i (toK D.nd i)) g (e u)

def residualBlockSum (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    Representation (kk D.nd i) (GE D.nd) ((Fin D.R.r → kk D.nd i) × (Fin D.R.t → kk D.nd i)) :=
  blockSum (matAlong D i (IsLocalRing.residue (D.nd.O i)) ρ)
    (chiAlong D i (IsLocalRing.residue (D.nd.O i)))

def ResidualShape (r : RepFam D i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  (∀ x, IsSemisimplificationOf (residualBlockSum D i ρ) (redK D i (r x))) ∧
    IsIrred (redK D i ρ) ∧ 1 < D.R.r

def ResidualShapeAt : Prop :=
  ∀ r : RepFam D i, GoodR D.nd i r → ∀ x₀, GoodRowPoint D i x₀ →
    (∃ ρ, OffBlock D i (r x₀) ρ) ∧ ∀ ρ, OffBlock D i (r x₀) ρ → ResidualShape D i r ρ

end Loc

def TypeHypothesis (D : D7) : Prop := 100 ≤ D.R.r ∧ ∀ k, 2 * D.R.r ≤ D.host.g k

def Constituents_at (D : D7) : Prop := ∀ i, ConstituentsAt D i

def ResidualShape_at (D : D7) : Prop := TypeHypothesis D → ∀ i, ResidualShapeAt D i

def ConstituentsAndShape_at (D : D7) : Prop := Constituents_at D ∧ ResidualShape_at D

def ConstituentsAndShapeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstituentsAndShape_at (Fm.D x i)

def ConstituentsAndShape (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstituentsAndShapeF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor' (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

def SplitRowF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, SplitRow_at (Fm.D x i)

def SplitRowClosed (C : FamClass) : Prop := Closed C (fun Fm _ => SplitRowF Fm)

example {R : Ranks} (H : Host R) : ∃ l, SplitRowPrime H l := by
  have hd : H.d ≠ 0 := H.hyp.2.1.ne_zero
  obtain ⟨l, hl, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one
    (5 + H.q + H.d + H.g 0 + H.g 1 + H.small.sup id) (k := 4 * H.d) (by omega)
  have hs : l ∉ H.small := fun h => by
    have : l ≤ H.small.sup id := Finset.le_sup (f := id) h
    omega
  have hq : l ≠ H.q := by omega
  have hd' : l ≠ H.d := by omega
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hj : jacobiSym (-(H.d : ℤ)) l = 1 := by
    rw [jacobiSym.mod_right _ hodd]
    have h1 : l % (4 * (-(H.d : ℤ)).natAbs) = 1 := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      have h := hmod
      unfold Nat.ModEq at h
      rw [h]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, jacobiSym.one_right]
  refine ⟨l, hl, by omega, hq, hd', ?_, ?_⟩
  · intro k
    fin_cases k
    · show l ≠ H.g 0
      omega
    · show l ≠ H.g 1
      omega
  · unfold Host.cls primeClass
    rw [if_neg hs, if_neg hq, if_neg hd', if_pos hj]

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
end

