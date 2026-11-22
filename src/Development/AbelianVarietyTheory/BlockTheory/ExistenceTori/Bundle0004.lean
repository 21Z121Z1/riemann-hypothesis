import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.IntegralFrameAcquisition
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsFiniteValuedExt (T T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) : Prop :=
  j.Finite ∧ 0 < r ∧ ∀ x : T.Fr, vV T'.V (j x) = (r : ℤ) * vV T.V x

def algHomOver {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (io : K →+* A) (j : A →+* B) :
    letI := io.toAlgebra
    letI := (j.comp io).toAlgebra
    A →ₐ[K] B :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  { j with commutes' := fun _ => rfl }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsIntegralFrameOf {T T' : CDVR} {io : c.F →+* T.Fr} (j : T.Fr →+* T'.Fr)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y' : IntFr Xo c T' (j.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  ∃ (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ), FrMap (algHomOver io j) y z ∧ FrBor t z y'.1

def AcquiresIntegralFrame (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (e : ℕ)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) : Prop :=
  ∃ (T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' (j.comp io)),
    IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) ∧ y'.IsAlg ∧ IsIntegralFrameOf j y y'

variable (Xo c)

def AllAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr), AcquiresIntegralFrame la e y

def AllTestAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
        (letI := io.toAlgebra
         FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) →
        AcquiresIntegralFrame la e y

variable {Xo c}

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ModelFamilies
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev tyOf (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Fin g → (E →+* ℂ) := fun j => relab c σ (e j).1

abbrev FamAt (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (tyOf c σ e)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}

structure ModelsOf (F : FamAt Xo c σ e) (r : ℕ) where

  X : Fin F.n → Data E r

  φ : ∀ k, (F.Di k).La ≃ₗ[𝓞 E] (X k).Λ

variable {F : FamAt Xo c σ e} {r : ℕ}

def ModelsOf.vec (M : ModelsOf F r) (k : Fin F.n) (a : (F.Di k).La) : Fin r → E := (M.φ k a : Fin r → E)

structure ModelBase (M : ModelsOf F r) : Prop where
  rank : r = Dw.p + Dw.q
  p0 : ∀ k, (M.X k).p0 = Dw.q
  cm : ∀ k (τ : E →+* ℂ), τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k (la : Wt (M.X k).Ψ r), ∀ γ ∈ (M.X k).Γ, (M.X k).χ la γ = 1
  lat : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.vec k a) (M.vec k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔
    IsUStab (M.X k).Gm (M.X k).Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (M.vec k a) = M.vec k (a + l.M • b)) ∧
      ∀ a, ∃ b : (F.Di k).La, (γ : Matrix (Fin r) (Fin r) E).mulVec (M.vec k a) = M.vec k (a + l.A • b)
  dom_bor : ∀ k, ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom
  dom_gam : ∀ k, ∀ x ∈ (M.X k).dom, ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom

theorem perFr_add (X : Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := fun ρ => by
    funext a; simp [Data.emb]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_add]; rfl
  · simp
  · rw [he]; simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

def pmOf (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun a j => perFr (M.X k) x (M.vec k a) (relab c σ (e j).1) (e j).2) (fun a b => by
    funext j
    have h : M.vec k (a + b) = M.vec k a + M.vec k b := by simp [ModelsOf.vec]
    rw [h, perFr_add]; rfl)

theorem pmOf_apply (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) (a : (F.Di k).La) (j : Fin g) :
    pmOf M k x a j = perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2 := rfl

def XiSign (M : ModelsOf F r) : Prop := ∀ k, ∀ τ ∈ (M.X k).Ψ, (τ (M.X k).ξ0).im < 0

theorem xiSign_of_kappa (M : ModelsOf F r) (h : ∀ k, (M.X k).κ0 = 2 * (M.X k).ξ0) : XiSign M := by
  intro k τ hτ
  have h1 := (M.X k).κ0_sign ⟨τ, hτ⟩
  rw [h k] at h1
  have h2 : τ 2 = 2 := map_ofNat τ 2
  simp [h2] at h1
  linarith

def PerDom (M : ModelsOf F r) : Prop :=
  ∀ k, ∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (tyOf c σ e) (pmOf M k x)

def PerOntoX (M : ModelsOf F r) : Prop :=
  ∀ k (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (tyOf c σ e) P → ∃ x ∈ (M.X k).dom, pmOf M k x = P

def PerDomSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamAt Xo c σ e) (r : ℕ) (M : ModelsOf F r),
    GoodEmb c σ → ModelBase M → XiSign M → PerDom M

def PerOntoXSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamAt Xo c σ e) (r : ℕ) (M : ModelsOf F r),
    GoodEmb c σ → ModelBase M → XiSign M → PerOntoX M

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
end
end

