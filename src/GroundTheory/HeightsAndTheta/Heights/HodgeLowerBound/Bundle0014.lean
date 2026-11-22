import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.TorusInvariantK0RegCusp
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineModel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagComplexPointsOverX
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

section Roots

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

abbrev Rts : Type := MvPolynomial (Ψ × Fin N) ℚ

variable {Ψ N}

def lin (la : Ψ × Fin N → ℤ) : Rts Ψ N := ∑ x, C (la x : ℚ) * X x

def la0 (j : ℕ) : Ψ × Fin N → ℤ := fun x => if (x.2 : ℕ) < j then 0 else -1

def muPoly (j : ℕ) : Rts Ψ N := lin (la0 j)

def altRho {R : Type} [CommRing R] (r : ℕ) (v : Fin r → R) : R :=
  (Matrix.of fun i l : Fin r => v i ^ (r - 1 - (l : ℕ))).det

def yv (j : ℕ) (hj : j ≤ N) (τ : Ψ) : Fin j → Rts Ψ N := fun i => X (τ, ⟨i, by omega⟩)

def zv (j : ℕ) (τ : Ψ) : Fin (N - j) → Rts Ψ N := fun l => X (τ, ⟨j + l, by omega⟩)

def fibV (j : ℕ) (hj : j ≤ N) : Rts Ψ N := ∏ τ, altRho j (yv j hj τ) * altRho (N - j) (zv j τ)

def cf (n : ℕ) : ℚ := (-1) ^ n

def fib (j : ℕ) (hj : j ≤ N) (n : ℕ) : Rts Ψ N := C (cf n) * fibV j hj

def FA (j : ℕ) (hj : j ≤ N) (n : ℕ) : Rts Ψ N := muPoly j ^ (n + 1) * fib j hj n

def antisym (G : Finset (Equiv.Perm (Ψ × Fin N))) (g : Rts Ψ N) : Rts Ψ N :=
  ∑ w ∈ G, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w g

def G0 (j : ℕ) : Finset (Equiv.Perm (Ψ × Fin N)) :=
  Finset.univ.filter fun w => ∀ x, (w x).1 = x.1 ∧ (((w x).2 : ℕ) < j ↔ (x.2 : ℕ) < j)

def Gfull : Finset (Equiv.Perm (Ψ × Fin N)) :=
  Finset.univ.filter fun w => ∀ x, (w x).1 = x.1

def delta0 (j : ℕ) : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if (x.2 : ℕ) < j then (x.2 : ℕ) else (x.2 : ℕ) - j

def deltaFull : Ψ × Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun x => (x.2 : ℕ)

def fdeg (j : ℕ) (hj : j ≤ N) : ℚ := coeff (delta0 j) (antisym (G0 j) (fibV (Ψ := Ψ) j hj))

def Jint (j : ℕ) (hj : j ≤ N) (n : ℕ) : ℚ :=
  coeff deltaFull (antisym Gfull (muPoly (Ψ := Ψ) (N := N) j ^ n * fib j hj n))

end Roots

section Polar

variable {σ : Type} [Fintype σ] [DecidableEq σ]

def polar (d : ℕ) (Pf : (σ → ℤ) → ℝ) (α : σ →₀ ℕ) : ℝ :=
  if (α.sum fun _ m => m) = d then
    (1 / (d.factorial : ℝ)) * ∑ β ∈ Finset.Iic α,
      (-1 : ℝ) ^ (d - β.sum fun _ m => m) * (∏ x, ((α x).choose (β x) : ℝ)) * Pf (fun x => (β x : ℤ))
  else 0

def PP (d : ℕ) (Pf : (σ → ℤ) → ℝ) (F : MvPolynomial σ ℚ) : ℝ :=
  ∑ α ∈ F.support, ((coeff α F : ℚ) : ℝ) * polar d Pf α

end Polar

section Y0

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

namespace ComponentData

variable (D : ComponentData Ψ K ι)

def flagGenericMatrix (τ : Ψ) : Matrix (Fin D.N) (Fin D.N1) (MvPolynomial (Ψ × Fin D.N × Fin D.N) (FnField D.P)) :=
  Matrix.of fun a l =>
    if (a : ℕ) < D.N - D.j then
      ∑ b : Fin (D.N - D.j), X (τ, a, ⟨b, by have := b.2; omega⟩) * C (D.hodge τ b l)
    else ∑ b : Fin D.N, X (τ, a, b) * C (D.basis τ b l)

def flagGenericPointMap : MRing (FlagBundleBlocksOverX ι Ψ D.N1 D.N) →+* MvPolynomial (Ψ × Fin D.N × Fin D.N) (FnField D.P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt D.P ⟨k, i⟩)
    | ⟨.inr q, S⟩ => flagMinor (D.flagGenericMatrix q.1) q.2 S

def flagBundleIdeal : Ideal (MRing (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) := RingHom.ker D.flagGenericPointMap

def flagBundleDimension : ℕ := D.n + D.f * (D.j * (D.j - 1) / 2 + D.jp * (D.jp - 1) / 2)

def xPart (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : Cone ι := fun p => w ⟨.inl p.1, p.2⟩

def flagComplexPointsOverX : Set (Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) := {w | w ∈ mcPts D.flagBundleIdeal ∧ D.xPart w ∈ D.Xo}

def liftX (A : HermLine ι) : HermLine (FlagBundleBlocksOverX ι Ψ D.N1 D.N) where
  a := Sum.elim A.a 0
  h w := A.h (D.xPart w)
  pos w hw := A.pos _ fun k => hw (Sum.inl k)
  smul c w hc := by
    have e : D.xPart (fun p => c p.1 * w p) = fun p => (fun k => c (Sum.inl k)) p.1 * D.xPart w p := rfl
    rw [e, A.smul _ _ (fun k => hc _), Fintype.prod_sum_type]
    simp

def cCoef (la : Ψ × Fin D.N → ℤ) (τ : Ψ) (r : Fin D.N) : ℤ :=
  if h : (r : ℕ) + 1 < D.N then la (τ, ⟨D.N - r - 1, by omega⟩) - la (τ, ⟨D.N - r - 2, by omega⟩)
  else -la (τ, ⟨0, by have := r.2; omega⟩)

def lineDeg (τ : Ψ) (r : Fin D.N) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  if h : (r : ℕ) + 1 < D.N then
    Sum.elim (fun k => -(((r : ℤ) + 1) * D.twist τ k)) (fun q => if q = (τ, ⟨r, by omega⟩) then 1 else 0)
  else Sum.elim (D.detLine τ).a 0

def flagDegreeVector (la : Ψ × Fin D.N → ℤ) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  ∑ x : Ψ × Fin D.N, D.cCoef la x.1 x.2 • D.lineDeg x.1 x.2

def regWeight (la : Ψ × Fin D.N → ℤ) (t : ℝ) (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : ℝ :=
  ∑ x : Ψ × Fin D.N, (D.cCoef la x.1 x.2 : ℝ) * D.regFl t x.1 x.2 w

omit [DecidableEq Ψ] in
theorem regWeight_inv (la : Ψ × Fin D.N → ℤ) (t : ℝ) : IsTorusInv (D.regWeight la t) := fun c w hc => by
  simp only [regWeight, D.regFl_inv _ _ _ c w hc]

def verticalLatticeBundle (B : ℕ) (la : Ψ × Fin D.N → ℤ) : HermLine ι :=
  tensorList ((D.SB B).toList.flatMap fun p =>
    (Finset.univ : Finset (Ψ × Fin D.N)).toList.map fun x => hzpow (D.latFl p x.1 x.2) (D.cCoef la x.1 x.2))

def LT (B : ℕ) (la : Ψ × Fin D.N → ℤ) (t : ℝ) : HermLine (FlagBundleBlocksOverX ι Ψ D.N1 D.N) :=
  (htwist (fsLine (D.flagDegreeVector la)) (D.regWeight la t) (D.regWeight_inv la t)).tensor (D.liftX (D.verticalLatticeBundle B la))

def PB (II : IntersectionSystem) (B : ℕ) (la : Ψ × Fin D.N → ℤ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun t =>
    II (K ⊕ (Ψ × Fin (D.N - 1))) (FlagBundleBlocksOverX ι Ψ D.N1 D.N) D.flagBundleIdeal (D.flagBundleDimension + 1) (fun _ => D.LT B la t)

omit [DecidableEq Ψ] in
theorem j_le_N : D.j ≤ D.N := D.j_lt_N.le

def FA' : Rts Ψ D.N := FA D.j D.j_le_N D.n

def PPB (II : IntersectionSystem) (B : ℕ) : ℝ := PP (D.flagBundleDimension + 1) (D.PB II B) D.FA'

def fdeg' : ℚ := fdeg (Ψ := Ψ) D.j D.j_le_N

def J' : ℚ := Jint (Ψ := Ψ) D.j D.j_le_N D.n

def plNormSq {N1 m : ℕ} (H : Matrix (Fin N1) (Fin N1) ℂ) (p : {S : Finset (Fin N1) // S.card = m} → ℂ) : ℝ :=
  (∑ S, ∑ S', star (p S) * (H.submatrix (S.1.orderEmbOfFin S.2) (S'.1.orderEmbOfFin S'.2)).det * p S').re

def hodgeLineW (τ : Ψ) (r : Fin D.N) (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : ℝ :=
  if h : (r : ℕ) + 1 < D.N then
    (1 / 2) * Real.log (plNormSq (D.metric τ (D.xPart w))
        (fun S : PluckerBlocks D.N1 D.N ⟨r, by omega⟩ => w ⟨Sum.inr (τ, ⟨r, by omega⟩), S⟩)) -
      Real.log ((fsLine (D.lineDeg τ r)).h w)
  else Real.log ((D.detLine τ).h (D.xPart w)) - Real.log ((fsLine (D.lineDeg τ r)).h w)

end ComponentData

end Y0

section FlZ

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

abbrev FlZBlk : Ψ × Fin (N - 1) → Type := fun q => PluckerBlocks N N q.2

def genT (τ : Ψ) : Matrix (Fin N) (Fin N) (MvPolynomial (Ψ × Fin N × Fin N) ℤ) := Matrix.of fun a b => X (τ, a, b)

def flZMap : MRing (FlZBlk Ψ N) →+* MvPolynomial (Ψ × Fin N × Fin N) ℤ :=
  eval₂Hom (Int.castRingHom _) fun q => flagMinor (genT Ψ N q.1.1) q.1.2 q.2

def FlZIdeal : Ideal (MRing (FlZBlk Ψ N)) := RingHom.ker (flZMap Ψ N)

def dimFl : ℕ := Fintype.card Ψ * (N * (N - 1) / 2)

variable {Ψ N}

def flDeg (la : Ψ × Fin N → ℤ) : Ψ × Fin (N - 1) → ℤ :=
  fun q => la (q.1, ⟨q.2 + 1, by omega⟩) - la (q.1, ⟨q.2, by omega⟩)

def PFl (II : IntersectionSystem) (la : Ψ × Fin N → ℤ) : ℝ :=
  II (Ψ × Fin (N - 1)) (FlZBlk Ψ N) (FlZIdeal Ψ N) (dimFl Ψ N + 1) (fun _ => fsLine (flDeg la))

def hFl (II : IntersectionSystem) (F : Rts Ψ N) : ℝ := PP (dimFl Ψ N + 1) (PFl II) F

end FlZ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AmpleOnGenericFibre (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def OffBoundary (Bd : Set ((Σ k, ι k) → ℂ)) (W : Ideal (MRing ι)) : Prop :=
  ∀ z ∈ mcPts W, z ∉ Bd

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure ComponentSetting (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] where

  H : HodgeData D

  Cd : CuspData D O Lt

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)

  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)

  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

namespace ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt)

abbrev MUq (B p q : ℕ) (t' : ℝ) : HermLine ι := MUc X.H X.S' B p q t'

def La (B : ℕ) : ℝ := abelian₂ B X.rd X.Lval

end ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def CuspBundlePos (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def HtInterior (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def HtBoundary (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def CuspMean (Cu : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    meanU X.H X.Cd ≤ Cu * D.f * D.j' * X.La B

def StokesLimit.Hyp (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℚ) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 → 0 < Jint Ψ N j cf →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ e) →
    -hFl Ψ N II (FA Ψ N j cf) ≤
      ((dimN Ψ N j + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (Fintype.card Ψ : ℝ) * e

def MUConjInvariant (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (X.MUq B p q t')

def slX (X : ComponentSetting D O Lt) (B : ℕ) : ℝ :=
  arLim X.H X.S B / (((D.n + 1 : ℕ) : ℝ) * degMu X.H)

def LowerBoundComponent.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (Ch Cu : ℝ),
    IsIntersectionSystem II → CuspBundlePos X → MUConjInvariant X → HtInterior Ch X → HtBoundary Ch X →
    CuspMean Cu X → 0 < degMu X.H → 3 * D.j' + 1 ≤ D.N →
    ∀ B : ℕ, 4 * D.f + 2 ≤ B → 4 * D.f * D.N ^ 2 ≤ B → ArLimExists X.H X.S B →
      -((Ch + Cu / 2) * D.f * D.j' * X.La B) ≤ slX X B

namespace Line

theorem grassmannianHeightZTwo_hypotheses :
    2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ 0 < Jint Unit 2 1 (-1) ∧
    ∀ Z : Matrix (Fin (2 - 1)) (Fin 1) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ 1 / 2 * Real.log 2 := by
  refine ⟨le_rfl, le_rfl, le_rfl, by rw [Jint_line]; norm_num, fun Z hZ => le_of_eq ?_⟩
  have h1 : ‖Z 0 0‖ = 1 := hZ 0 0
  have hdet : (1 + Z * Z.conjTranspose).det = 1 + Z 0 0 * starRingEnd ℂ (Z 0 0) := by
    have h := Matrix.det_fin_one (1 + Z * Z.conjTranspose : Matrix (Fin 1) (Fin 1) ℂ)
    refine h.trans ?_
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hdet, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def projLineComponentSetting : ComponentSetting (lineData II hII) GaussianInt GaussianInt where
  H := lineHodge II hII
  Cd := gaussCusp II hII
  M := lineModel
  S := lineRegT II hII
  S_tied := lineRegT_tied II hII
  S' := lineBRegC II hII
  S'_tied := lineBRegC_tied II hII
  rd := 1
  Lval := 0

theorem projLineComponentSetting_La (B : ℕ) : (projLineComponentSetting II hII).La B = Real.log B := by
  simp [ComponentSetting.La, projLineComponentSetting, abelian₂]

theorem zero_hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ zeroSystem Unit (PBlk 2) W 1 ![fsLine 2] :=
  fun _ _ => le_rfl

theorem htInterior_line : HtInterior 1 (projLineComponentSetting zeroSystem zero_hII) := by
  intro B p q hB _ _
  refine ⟨1, one_pos, fun t' _ _ W _ _ _ => ?_⟩
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := le_trans (by norm_num [lineData, ComponentData.f]) hB
    exact_mod_cast this
  have hL : 0 ≤ Real.log B := Real.log_nonneg hB1
  rw [projLineComponentSetting_La]
  have h0 : htMUc (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S' B p q t' W = 0 := by
    simp [htMUc, zeroSystem]
  rw [h0]
  have hKA : (lineData zeroSystem zero_hII).KA = 0 := rfl
  rw [hKA]
  have : (0 : ℝ) ≤ 1 * ((lineData zeroSystem zero_hII).f : ℝ) * ((lineData zeroSystem zero_hII).j' : ℝ) *
      Real.log B := by
    have hf : ((lineData zeroSystem zero_hII).f : ℝ) = 1 := by norm_num [ComponentData.f]
    have hj : ((lineData zeroSystem zero_hII).j' : ℝ) = 1 := by norm_num [ComponentData.j', lineData]
    rw [hf, hj]; linarith
  linarith

theorem htBoundary_line : HtBoundary 1 (projLineComponentSetting zeroSystem zero_hII) := by
  intro B p q hB hp hpq
  obtain ⟨t₀, ht₀, h⟩ := htInterior_line B p q hB hp hpq
  exact ⟨t₀, ht₀, fun t' ht0 ht1 W hW hXW _ => h t' ht0 ht1 W hW hXW fun z _ => Set.notMem_empty z⟩

theorem cuspMean_line : CuspMean 1 (projLineComponentSetting II hII) := by
  intro _ _ B hB
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := le_trans (by norm_num [lineData, ComponentData.f]) hB
    exact_mod_cast this
  rw [projLineComponentSetting_La]
  have h0 : meanU (projLineComponentSetting II hII).H (projLineComponentSetting II hII).Cd = 0 := meanU_line
  rw [h0]
  have hf : ((lineData II hII).f : ℝ) = 1 := by norm_num [ComponentData.f]
  have hj : ((lineData II hII).j' : ℝ) = 1 := by norm_num [ComponentData.j', lineData]
  rw [hf, hj]
  have := Real.log_nonneg hB1
  linarith

theorem stokesLimit_hyp_line (B : ℕ) : StokesLimit.Hyp (projLineComponentSetting zeroSystem zero_hII) B 0 := by
  intro p q _ _
  refine ⟨1, one_pos, fun t' _ _ => ?_⟩
  have hKA : (lineData zeroSystem zero_hII).KA = 0 := rfl
  have h0 : topMUc (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S' B p q t' = 0 := by
    simp [topMUc, zeroSystem]
  rw [h0, hKA]
  simp

theorem arLimExists_line (B : ℕ) :
    ArLimExists (projLineComponentSetting zeroSystem zero_hII).H (projLineComponentSetting zeroSystem zero_hII).S B :=
  ⟨0, tendsto_const_nhds⟩

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

abbrev GenFrac (F : Type) [Field F] (Ψ : Type) (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Ψ × Fin n × Fin n) F)

def genMatFr (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b =>
    algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (X (τ, a, b))

def flagMinorRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : Ψ × Σ j : Fin (n - 1), PluckerBlocks n n j) :
    GenFrac F Ψ n :=
  flagMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2 / leadMinor (genMatFr F Ψ n q.1) q.2.1

abbrev PivotIdx (Ψ : Type) (n : ℕ) : Type := Ψ × Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) < b}

def pivotRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : PivotIdx Ψ n) : GenFrac F Ψ n :=
  pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / leadMinor (genMatFr F Ψ n q.1) q.2.1

theorem PlueckerData.ofΩ_eq {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)
    (x : Ω) : Pl.ofΩ x = algebraMap Ω (GenFrac Ω Ψ D.N) x := by
  rw [PlueckerData.ofΩ, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Ω (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) (GenFrac Ω Ψ D.N)]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}

theorem LogLogRegularisationSetting.eventually_closedBall_subset (S : LogLogRegularisationSetting M Xo A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.R.mid j),
      closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.R.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
    hc.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
  have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.R.chart j).map_source (S.R.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem LogLogRegularisationSetting.eventually_chartLevi (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ k : Fin S.R.N, ∀ x ∈ S.R.mid k, ∀ w : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖w‖ ^ 2 ≤
          levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k x) w := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.GlueRegularised.full M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

