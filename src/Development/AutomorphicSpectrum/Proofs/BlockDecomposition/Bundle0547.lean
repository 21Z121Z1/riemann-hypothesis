import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Moderate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc Model Rep Base Geo Chars RealMaps FinMaps pure PolMatch IsMatched Decay OneConst Coinv IsConst)
open GlobalTheory.WeilM (SB schA)

variable {D : D7}

def polSpan {n d : ℕ} {Y : Spc D.host.F D.host.E n} {Z : Spc D.host.F D.host.E d} (Mo : Model D.sp.cm.sig Y Z)
    (Bs : Base D.host.F D.host.E) : Submodule ℂ ((Fin n × Fin d → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) ∧
    f ∈ Mo.Pol Bs.ψ Bs.emb ∧ Φ = pure f φ}

structure PairSit (ε : Bool) {M X : HSp D} (θ : InfFam D) (A : Fr M) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) {Y : Spc D.host.F D.host.E M.rank} {Z : Spc D.host.F D.host.E d}
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X) : Prop where

  fam : IsInfFam θ

  base : Bs.IsGood D.sp.cm.sig

  good : Mo.IsGood Bs.ψ

  weilD : Mo.IsWeil Bs.ψ χ₁ χ₂ om

  weil : IsWeil Bs.ψ ε M X χ₁ χ₂ ω

  dict : IsDict (ε := ε) e Bs.ψ ω Mo om c hY hZ

  herm : ∃ r s, Y.IsHerm D.sp.cm.sig Bs r s

  skew : ∃ r s, Z.IsSkew D.sp.cm.sig Bs r s

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Y.θ w = (if ε then (1 : ℂ) else -1) • A.cart τ ∧
    Z.θ w = (reindex e e (B.cart τ)).map conj

structure Sit {W W₁ X : HSp D} (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank) : Prop where

  fam : IsInfFam θ

  tri : IsTriple W W₁ X α β

  hν : IsHaarFD W ν 𝓕

  hν₁ : IsHaarFD W₁ ν₁ 𝓕₁

  weilA : IsWeil Bs.ψ true W X β (β / α) ωA

  weilB : IsWeil Bs.ψ false W₁ X α (α / β) ωB

  read : IsReading Bs.ψ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ Bs Γ Xc

  dictA : IsDict (ε := true) e Bs.ψ ωA Γ.M om 1 read.JW read.JX

  dictB : IsDict (ε := false) e Bs.ψ ωB Γ.M' om' (-1) read.JW₁ read.JX

  matched : IsMatched Bs Γ Xc om om' R Rf

  decay : Decay Bs Γ om om'

  const : OneConst Bs Γ Xc om om' R Rf

  coinv : Coinv Bs Γ Xc om om' Rf

def ThetaLin : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    polSpan Mo Bs ≤ schA D.host.F (Fin M.rank × Fin d) ∧
    (∀ Φ₁ ∈ schA D.host.F (Fin M.rank × Fin d), ∀ Φ₂ ∈ schA D.host.F (Fin M.rank × Fin d),
      thetaOf (ε := ε) e Mo Bs.ψ (Φ₁ + Φ₂) = thetaOf (ε := ε) e Mo Bs.ψ Φ₁ + thetaOf (ε := ε) e Mo Bs.ψ Φ₂) ∧
    ∀ (s : ℂ), ∀ Φ ∈ schA D.host.F (Fin M.rank × Fin d),
      thetaOf (ε := ε) e Mo Bs.ψ (s • Φ) = s • thetaOf (ε := ε) e Mo Bs.ψ Φ

def AlgOf : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    ∀ Φ ∈ polSpan Mo Bs, thetaOf (ε := ε) e Mo Bs.ψ Φ ∈ algF Bs.ψ θ ε A B

def AlgTo : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    ∀ f ∈ algF Bs.ψ θ ε A B, ∃ Φ ∈ polSpan Mo Bs, thetaOf (ε := ε) e Mo Bs.ψ Φ = f

def Maps : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
      (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
      IsMatch Bs.ψ θ A A₁ B α β ωA ωB Pi rf rl p p' ∧
      ∀ Φ ∈ polSpan Γ.M Bs, ∀ Φ' ∈ polSpan Γ.M' Bs,
        p (thetaOf (ε := true) e Γ.M Bs.ψ Φ) = p' (thetaOf (ε := false) e Γ.M' Bs.ψ Φ') → PolMatch Bs Γ Xc R Rf Φ Φ'

def Closure : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ Φ ∈ polSpan Γ.M' Bs, ∃ Φ₀ ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁,
      thetaOf (ε := false) e Γ.M' Bs.ψ Φ - thetaOf (ε := false) e Γ.M' Bs.ψ Φ₀ ∈ finRel ωB (algF Bs.ψ θ false A₁ B)

def Moderate : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ Φ ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁, ModInt θ ωB ν₁ 𝓕₁ (thetaOf (ε := false) e Γ.M' Bs.ψ Φ)

def ConstEq : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ c : ℂ, IsConst Bs Γ Xc om om' R Rf c → ∀ Φ ∈ polSpan Γ.M Bs, ∀ Φ' ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁,
      PolMatch Bs Γ Xc R Rf Φ Φ' →
      thetaInt ωA ν 𝓕 (thetaOf (ε := true) e Γ.M Bs.ψ Φ) = c • thetaInt ωB ν₁ 𝓕₁ (thetaOf (ε := false) e Γ.M' Bs.ψ Φ')

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Onto

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_comp_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    Geo.mCoordIdeal (fun p => j (w p)) = Geo.mCoordIdeal w := by
  have key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Geo.mConeMap]
  ext f
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

theorem mCoordIdeal_blockScale {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → Ω) :
    Geo.mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = Geo.mCoordIdeal z := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k) * X k
  let φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k)⁻¹ * X k
  have hinv : φ'.comp φ = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg φ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at this
  have hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g) := by
    intro g
    have : Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C,
        algebraMap_eq]
      ring
    rw [this]; rfl
  ext g
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]

theorem mCoordIdeal_of_ker {Ω : Type} [Field Ω] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (φ : Geo.MRing ι →+* Ω) (hφ : RingHom.ker φ = P) : Geo.mCoordIdeal (fun p => φ (X p)) = P := by
  have hev : ∀ f, aeval (fun p => φ (X p)) f = φ f := by
    intro f
    have : ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ :=
      MvPolynomial.ringHom_ext
        (fun r => RingHom.congr_fun (Subsingleton.elim
          (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r)
        (fun p => by simp)
    exact congrArg (fun ψ => ψ f) this
  apply le_antisymm
  · intro f hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf
    have e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp
        (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [Geo.mConeMap]
    have := congrArg (fun ψ => ψ f) e
    simp only [AlgHom.comp_apply, hf, map_zero, hev] at this
    rw [← hφ, RingHom.mem_ker]
    exact this.symm
  · have hP' := hP
    obtain ⟨S, hS, hPS⟩ := hP'
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h0 : φ f = 0 := by
      rw [← RingHom.mem_ker, hφ, hPS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]

end Coord

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem exists_ptIdeal_eq_mCoordIdeal {F : Type} [Field F] (v : (Σ k, Bk n k) → F)
    (hv : ∀ k, ∃ i, v ⟨k, i⟩ ≠ 0) : ∃ x : MP ℤ m n, ptIdeal x = Geo.mCoordIdeal v := by
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hv k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp F ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
  have ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F) := fun k =>
    GlobalTheory.ProjSpace.pt_str _ _ _
  let g : Sp F ⟶ MP ℤ m n := ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha
  have hg : ∀ k, g ≫ prB n k = a k := fun k => ProjSpace.lift_pr m n _ a ha k
  let p : Sp F := IsLocalRing.closedPoint F
  let x : MP ℤ m n := g p
  let θ : F →+* (Sp F).residueField p :=
    ((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp F).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  refine ⟨x, ?_⟩
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v,
    ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_ptIdeal_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Geo.MRing (Bk n)))
    (hP : Geo.IsMultiProjPrime P) : ∃ x : MP ℤ m n, ptIdeal x = P := by
  obtain ⟨hp, hh, hr⟩ := hP
  let φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P) :=
    (algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)
  have hφ : RingHom.ker φ = P := by
    ext f
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
      (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
  have hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hφ, RingHom.mem_ker]
    exact h0
  obtain ⟨x, hx⟩ := exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv
  exact ⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩

end GlobalTheory.CompanionTheory.MPDict.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitNormLocal

open IsLocalRing

theorem exists_conj_mul_eq_of_residue_one {R : Type} [CommRing R] [HenselianLocalRing R]
    (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (x₀ : R) (hx : IsUnit (σ x₀ - x₀)) (a : R)
    (ha : a ∈ maximalIdeal R) (hfix : σ a = a) :
    ∃ s : R, σ s * s = 1 + a := by
  have hmax : ∀ y ∈ maximalIdeal R, σ y ∈ maximalIdeal R := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    exact fun h => hy (by simpa [hσ] using h.map σ)
  have hres : ∀ y, y - 1 ∈ maximalIdeal R → IsUnit y := by
    intro y hy
    by_contra h
    have h1 : y ∈ maximalIdeal R := (mem_maximalIdeal _).2 h
    have h2 : (1 : R) ∈ maximalIdeal R := by simpa using sub_mem h1 hy
    exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨d, hd⟩ := hx
  set di : R := ((d⁻¹ : Rˣ) : R) with hdi
  have hddi : (σ x₀ - x₀) * di = 1 := by rw [← hd, hdi]; exact d.mul_inv
  set e : R := -x₀ * di with he
  set f : R := σ e with hf
  have hσdi : σ di = -di := by
    have h1 : σ ((σ x₀ - x₀) * di) = 1 := by rw [hddi, map_one]
    rw [map_mul, map_sub, hσ] at h1
    linear_combination (-di) * h1 + (-σ di) * hddi
  have hef : e + f = 1 := by
    rw [hf, he, map_mul, map_neg, hσdi]
    linear_combination hddi
  have hfe : σ f = e := by rw [hf, hσ]
  set n : R := e * f with hn
  have hσn : σ n = n := by rw [hn, map_mul, hfe, ← hf]; ring
  let P : R[X] := X ^ 2 - X - C (n * a)
  have hP : P.Monic := by simp only [P]; monicity!
  have hP1 : P.eval 1 ∈ maximalIdeal R := by
    have : P.eval 1 = -(n * a) := by simp [P]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ ha)
  have hP2 : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (P.derivative.eval 1)) := by
    have : P.derivative.eval 1 = 1 := by
      simp [P, derivative_X_pow]
    rw [this, map_one]; exact isUnit_one
  obtain ⟨u, hu, hu1⟩ := HenselianRing.is_henselian (I := maximalIdeal R) P hP 1 hP1 (by exact hP2)
  have hroot : u ^ 2 - u = n * a := by
    have : P.eval u = 0 := hu
    simp only [P, eval_sub, eval_pow, eval_X, eval_C] at this
    linear_combination this
  have hroot' : (σ u) ^ 2 - σ u = n * a := by
    have := congrArg σ hroot
    simpa only [map_sub, map_pow, map_mul, hσn, hfix] using this
  have hv1 : σ u - 1 ∈ maximalIdeal R := by simpa using hmax _ hu1
  have hw : IsUnit (u + σ u - 1) := hres _ (by
    have := add_mem hu1 hv1
    convert this using 1
    ring)
  have huu : σ u = u := by
    have h0 : (u - σ u) * (u + σ u - 1) = 0 := by linear_combination hroot - hroot'
    have := hw.mul_left_eq_zero.1 h0
    exact (sub_eq_zero.1 this).symm
  obtain ⟨U, hU⟩ := hres u hu1
  set ui : R := ((U⁻¹ : Rˣ) : R) with hui
  have huui : u * ui = 1 := by rw [← hU, hui]; exact U.mul_inv
  have hσui : σ ui = ui := by
    have h1 : σ (u * ui) = 1 := by rw [huui, map_one]
    rw [map_mul, huu] at h1
    linear_combination ui * h1 - σ ui * huui
  have h2 : a * ui + n * (a * ui) ^ 2 = a := by
    linear_combination (-a * ui ^ 2) * hroot + (a * (ui * u + 1) - a * ui) * huui
  refine ⟨1 + e * (a * ui), ?_⟩
  have hσt : σ (a * ui) = a * ui := by rw [map_mul, hfix, hσui]
  rw [map_add, map_one, map_mul σ e, hσt, ← hf]
  linear_combination (a * ui) * hef + h2 - (a * ui) ^ 2 * hn

theorem exists_isUnit_conj_mul_eq {R : Type} [CommRing R] [HenselianLocalRing R]
    [Finite (ResidueField R)] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (x₀ : R)
    (hx : IsUnit (σ x₀ - x₀)) (c : R) (hc : IsUnit c) (hfix : σ c = c) :
    ∃ s : R, IsUnit s ∧ σ s * s = c := by
  haveI : IsLocalHom σ := ⟨fun a h => by simpa [hσ] using h.map σ⟩
  let τ : ResidueField R →+* ResidueField R := ResidueField.map σ
  have hτ : ∀ y, τ (residue R y) = residue R (σ y) := fun y => ResidueField.map_residue σ y
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    rw [hτ, hτ, hσ]
  have hne : ∃ x, τ x ≠ x := by
    refine ⟨residue R x₀, fun h => ?_⟩
    rw [hτ] at h
    have h0 : residue R (σ x₀ - x₀) = 0 := by rw [map_sub, h, sub_self]
    exact (residue_ne_zero_iff_isUnit _).2 hx h0
  obtain ⟨sb, hsb⟩ := GlobalTheory.CompanionTheory.FFNorm.exists_conj_mul_eq (ResidueField R) τ hτ2 hne (residue R c)
    (by rw [hτ, hfix])
  obtain ⟨s₀, rfl⟩ := residue_surjective sb
  rw [hτ, ← map_mul] at hsb
  have hs₀ : IsUnit s₀ := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    rw [map_mul, h0, mul_zero] at hsb
    exact (residue_ne_zero_iff_isUnit _).2 hc hsb.symm
  obtain ⟨D, hD⟩ := (hs₀.map σ).mul hs₀
  set Di : R := ((D⁻¹ : Rˣ) : R) with hDi
  have hDDi : σ s₀ * s₀ * Di = 1 := by rw [← hD, hDi]; exact D.mul_inv
  have hσD : σ (σ s₀ * s₀) = σ s₀ * s₀ := by rw [map_mul, hσ, mul_comm]
  have hσDi : σ Di = Di := by
    have h1 : σ (σ s₀ * s₀ * Di) = 1 := by rw [hDDi, map_one]
    rw [map_mul, hσD] at h1
    linear_combination Di * h1 - σ Di * hDDi
  have ha : c * Di - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hsb, ← map_mul, hDDi, map_one, sub_self]
  obtain ⟨s₁, hs₁⟩ := exists_conj_mul_eq_of_residue_one σ hσ x₀ hx _ ha
    (by rw [map_sub, map_mul, hfix, hσDi, map_one])
  have hmul : σ (s₀ * s₁) * (s₀ * s₁) = c := by
    rw [map_mul]
    linear_combination (σ s₀ * s₀) * hs₁ + c * hDDi
  refine ⟨s₀ * s₁, ?_, hmul⟩
  exact isUnit_of_mul_isUnit_right (hmul ▸ hc)

theorem exists_unit_norm_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ c : w.adicCompletion E, cj w c = c → Valued.v c = 1 → ∃ s : w.adicCompletion E, Valued.v s = 1 ∧ cj w s * s = c := by
  intro E _ _ _ hU w hw c hcj hcv
  obtain ⟨-, hinv, hval, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hI, -⟩, -, -⟩ := hns hw
  obtain ⟨-, -, -, -, ⟨x₀, hx₀, hx⟩, hq, hcard⟩ := hI
  haveI := Formalism.BasicNotions.Examples₂.adicInt_henselian (K := E) w
  have hfin : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := by
    refine Nat.finite_of_card_ne_zero ?_
    have h := hcard
    have h2 : q ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
    rw [← h] at h2
    exact h2
  have hmem : ∀ x : w.adicCompletionIntegers E, cj w x ∈ w.adicCompletionIntegers E := by
    intro x
    have hx2 := x.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx2 ⊢
    rwa [hval]
  let σ : w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
    ((cj w).comp (w.adicCompletionIntegers E).subtype).codRestrict _ hmem
  have hσc : ∀ x, ((σ x : w.adicCompletionIntegers E) : w.adicCompletion E) = cj w x := fun _ => rfl
  have hunit : ∀ x : w.adicCompletionIntegers E, IsUnit x ↔ Valued.v (x : w.adicCompletion E) = 1 :=
    fun x => (Formalism.BasicNotions.Examples₂.adicInt_integers w).isUnit_iff_valuation_eq_one
  have hσ : ∀ x, σ (σ x) = x := fun x => Subtype.ext (hinv _)
  let y₀ : w.adicCompletionIntegers E := ⟨x₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx₀⟩
  have hy : IsUnit (σ y₀ - y₀) := (hunit _).2 hx
  let c₀ : w.adicCompletionIntegers E := ⟨c, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hcv.le⟩
  have hc₀ : IsUnit c₀ := (hunit _).2 hcv
  obtain ⟨s, hs, hsc⟩ := exists_isUnit_conj_mul_eq σ hσ y₀ hy c₀ hc₀ (Subtype.ext hcj)
  exact ⟨s, (hunit s).1 hs, congrArg Subtype.val hsc⟩

end GlobalTheory.CompanionTheory.UnitNormLocal
end

