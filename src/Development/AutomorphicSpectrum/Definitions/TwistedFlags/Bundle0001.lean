import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0032

-- bundled from Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec eulerFac seg)
open Formalism.UG (qV IsUnifV dosetInd)

namespace GlobalTheory.CompanionTheory.Ipf.Val

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Cv : Type := v.adicCompletion K

def absV (x : Cv v) : ℝ := (WithZeroMulInt.toNNReal (NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ)

def IsPar (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))) : Prop :=
  ∀ k, k ∈ J ↔ k ∈ KGL v (r + c) ∧ ∀ i j, Valued.v (bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)) i j) < 1

def IsTame (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) ∧ ∀ x : (Cv v)ˣ, Valued.v ((x : Cv v) - 1) < 1 → δ x = 1

def IsRam (δ : (Cv v)ˣ →* ℂˣ) : Prop := ∃ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 ∧ δ x ≠ 1

def lamD {r c : ℕ} (δ : (Cv v)ˣ →* ℂˣ) (k : GL (Fin (r + c)) (Cv v)) : ℂ :=
  chi0 δ (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v))).det

def blk (r : ℕ) {c : ℕ} (m : GL (Fin c) (Cv v)) : GL (Fin (r + c)) (Cv v) := pEl (1 : GL (Fin r) (Cv v)) 0 m

def IsDiag {c : ℕ} (ϖ : Cv v) (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)) : Prop := m.1 = Matrix.diagonal fun i => ϖ ^ d i

def len {c : ℕ} (d : Fin c → ℤ) : ℕ := ∑ i, (d i).natAbs

def IsBlockDoubleCosetFunction {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) (m : GL (Fin c) (Cv v))
    (h : GL (Fin (r + c)) (Cv v) → ℂ) : Prop :=
  (∀ k₁ ∈ J, ∀ k₂ ∈ J, h (k₁ * blk v r m * k₂) = (lamD v δ k₁ * lamD v δ (blk v r m) * lamD v δ k₂)⁻¹) ∧
    ∀ g, g ∉ DoubleCoset.doubleCoset (blk v r m) (J : Set _) J → h g = 0

def IsSphEig {c : ℕ} (B : Multiset ℂˣ) (m : GL (Fin c) (Cv v)) (lam : ℂ) : Prop :=
  ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module ℂ V₀) (ρ₀ : Representation ℂ (GL (Fin c) (Cv v)) V₀) (x₀ : V₀),
    IsSatVecGL v ρ₀ x₀ B ∧ heckeVec ρ₀ (KGL v c) (dosetInd ℂ (KGL v c) m) x₀ = lam • x₀

def IsBlockVector {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ) : Prop :=
  B.card = c ∧ (∀ k ∈ J, ρ k x = lamD v δ k • x) ∧
    ∀ ϖ, IsUnifV K v ϖ → ∀ (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)), IsDiag v ϖ d m → ∀ lam, IsSphEig v B m lam →
      ∀ h, IsBlockDoubleCosetFunction v J δ m h → heckeVec ρ J h x = ((qV K v : ℂ) ^ ((r : ℂ) / 2 * len d) * lam) • x

def IsBlockKernel {r c : ℕ} (J : Subgroup (GL (Fin (r + c)) (Cv v))) (δ : (Cv v)ˣ →* ℂˣ) (X : ℂ)
    (κ : GL (Fin (r + c)) (Cv v) → ℂ) : Prop :=
  (∀ ϖ, IsUnifV K v ϖ → ∀ (d : Fin c → ℤ) (m : GL (Fin c) (Cv v)), IsDiag v ϖ d m → ∀ k₁ ∈ J, ∀ k₂ ∈ J,
    κ (k₁ * blk v r m * k₂) = (lamD v δ k₁ * lamD v δ (blk v r m) * lamD v δ k₂)⁻¹ * X ^ len d) ∧
    ∀ g, (∀ m : GL (Fin c) (Cv v), g ∉ DoubleCoset.doubleCoset (blk v r m) (J : Set _) J) → κ g = 0

def HasSph (c : ℕ) (B : Multiset ℂˣ) : Prop :=
  (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV K v : ℝ) ^ (((c : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV K v : ℝ) ^ (((c : ℝ) - 1) / 2)) ∧
  ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module ℂ V₀) (ρ₀ : Representation ℂ (GL (Fin c) (Cv v)) V₀) (x₀ : V₀)
    (ℓ : V₀ →ₗ[ℂ] ℂ), IsSatVecGL v ρ₀ x₀ B ∧ ℓ x₀ ≠ 0 ∧ (∃ C : ℝ, ∀ g, ‖ℓ (ρ₀ g x₀)‖ ≤ C) ∧
      ∀ m, ∃ lam : ℂ, heckeVec ρ₀ (KGL v c) (dosetInd ℂ (KGL v c) m) x₀ = lam • x₀

def phiB (δ : (Cv v)ˣ →* ℂˣ) (r d c : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) : ℂ :=
  open Classical in
  if (∀ i j, Valued.v (x i j) ≤ 1) ∧ Valued.v (bAA x).det = 1 ∧ ∀ i j, Valued.v (bDA x i j) < 1 then chi0 δ (bAA x).det else 0

def linAct {a b : ℕ} (δS δT : (Cv v)ˣ →* ℂˣ) (g : GL (Fin a) (Cv v)) (h : GL (Fin b) (Cv v))
    (Φ : Matrix (Fin b) (Fin a) (Cv v) → ℂ) : Matrix (Fin b) (Fin a) (Cv v) → ℂ :=
  fun y => (((δT (Matrix.GeneralLinearGroup.det g))⁻¹ * δS (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
    ((absV v g.1.det ^ ((b : ℝ) / 2) * absV v h.1.det ^ (-(a : ℝ) / 2) : ℝ) : ℂ) * Φ ((h⁻¹).1 * y * g.1)

end Local

def lFac (q : ℕ) (B : Multiset ℂˣ) (s : ℂ) : ℂ :=
  eulerFac B ((q : ℂ) ^ (-(s + 1 / 2))) * eulerFac (B.map (·⁻¹)) ((q : ℂ) ^ (-(s + 1 / 2)))

def qFac (q c : ℕ) (B : Multiset ℂˣ) (s : ℂ) : ℂ :=
  lFac q B s * ∏ i ∈ Finset.range c, (1 - (q : ℂ) ^ (-(2 * s + c - i)))

def BlockDoubleCosetFunctionsExist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ),
    (∃ J, IsPar v r c J) ∧ ∀ J, IsPar v r c J → ∀ δ, IsTame v δ → ∀ m, ∃ h, IsBlockDoubleCosetFunction v J δ m h

def SphEigUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (B : Multiset ℂˣ), B.card = c →
    ∀ m : GL (Fin c) (Cv v), ∃! lam, IsSphEig v B m lam

def SphStrings : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k t : ℕ) (x : ℕ → ℂˣ), (∀ i, ‖(x i : ℂ)‖ = 1) →
    HasSph v (k * t) (∑ i ∈ Finset.range k, seg v (x i) t)

def QSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δ, IsTame v δ → ∀ (s : ℂ) (κ : GL (Fin (r + c)) (Cv v) → ℂ), (c : ℝ) / 2 < s.re →
    IsBlockKernel v J δ ((qV K v : ℂ) ^ (-(((r : ℂ) + c) / 2 + s))) κ →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ),
      IsBlockVector v J δ ρ x B → HasSph v c B → ∀ ℓ : X →ₗ[ℂ] ℂ,
      Summable (fun y : GL (Fin (r + c)) (Cv v) ⧸ J => κ y.out * ℓ (ρ y.out x)) →
        HasSum (fun y : GL (Fin (r + c)) (Cv v) ⧸ J => κ y.out * ℓ (ρ y.out x)) (qFac (qV K v) c B s * ℓ x)

def EquivSupp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r d c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v)))
    (J' : Subgroup (GL (Fin (r + d)) (Cv v))), IsPar v r c J → IsPar v r d J' → ∀ δ, IsTame v δ → IsRam v δ →
    ∀ Φ : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v) → ℂ,
      (∀ k ∈ J, ∀ k' ∈ J', ∀ y, Φ (k'.1 * y * k.1) = chi0 δ (bAA k'.1).det * chi0 δ (bAA k.1).det * Φ y) →
      ∀ y, Φ y ≠ 0 → ∃ k ∈ J, ∃ k' ∈ J', bAD (k'.1 * y * k.1) = 0 ∧ bDA (k'.1 * y * k.1) = 0 ∧ (bAA (k'.1 * y * k.1)).det ≠ 0

def SphMatchAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c t : ℕ) (ϖ : Cv v), IsUnifV K v ϖ →
    ∀ m' : GL (Fin (c + t)) (Cv v), ∃ (I : Finset (Fin c → ℤ)) (a : (Fin c → ℤ) → ℂ) (m : (Fin c → ℤ) → GL (Fin c) (Cv v)),
      (∀ e, IsDiag v ϖ e (m e)) ∧
      (∀ y, (∑ᶠ z : GL (Fin (c + t)) (Cv v) ⧸ KGL v (c + t), dosetInd ℂ (KGL v (c + t)) m' z.out *
          linAct v 1 1 (1 : GL (Fin c) (Cv v)) z.out (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) =
        ∑ e ∈ I, a e * ∑ᶠ z : GL (Fin c) (Cv v) ⧸ KGL v c, dosetInd ℂ (KGL v c) (m e) z.out *
          linAct v 1 1 z.out (1 : GL (Fin (c + t)) (Cv v)) (Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1) y) ∧
      ∀ (B : Multiset ℂˣ) (lam : (Fin c → ℤ) → ℂ), (∀ e, IsSphEig v B (m e)⁻¹ (lam e)) →
        IsSphEig v (B + seg v 1 t) m' (∑ e ∈ I, a e * lam e)

def BlockVectorLocalLift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c t : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v)))
    (J' : Subgroup (GL (Fin (r + (c + t))) (Cv v))), IsPar v r c J → IsPar v r (c + t) J' →
    ∀ δS δT, IsTame v δS → IsTame v δT → IsRam v δT → (∀ x : (Cv v)ˣ, Valued.v (x : Cv v) = 1 → δS x = δT x) →
    ∀ (Z X Y : Type) [AddCommGroup Z] [Module ℂ Z] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (j : Z →ₗ[ℂ] (Matrix (Fin (r + (c + t))) (Fin (r + c)) (Cv v) → ℂ)), Function.Injective j →
      ∀ ω : Representation ℂ (GL (Fin (r + c)) (Cv v) × GL (Fin (r + (c + t))) (Cv v)) Z,
      (∀ g h z, j (ω (g, h) z) = linAct v δS δT g h (j z)) → ∀ z₀, j z₀ = phiB v δT r (c + t) c →
      ∀ (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ), IsBlockVector v J δT ρ x B →
      ∀ p : Z →ₗ[ℂ] X →ₗ[ℂ] Y, (∀ g z x', p (ω (g, 1) z) (ρ g x') = p z x') →
        IsBlockVector v J' δS (GlobalTheory.PRep.rightReg ℂ (GL (Fin (r + (c + t))) (Cv v)) Y) (fun h => p (ω (1, h) z₀) x) (B + seg v 1 t)

def BlockUnramifiedTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δ ν : (Cv v)ˣ →* ℂˣ, IsTame v δ → IsTame v ν → ¬ IsRam v ν → ∀ z : ℂˣ,
    (∀ ϖ : (Cv v)ˣ, IsUnifV K v (ϖ : Cv v) → ν ϖ = z) →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin (r + c)) (Cv v)) X) (x : X) (B : Multiset ℂˣ),
      IsBlockVector v J δ ρ x B → IsBlockVector v J (δ * ν) ρ x (B.map (z⁻¹ * ·))

def KerLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (r d c : ℕ) (J : Subgroup (GL (Fin (r + c)) (Cv v))),
    IsPar v r c J → ∀ δS δT, IsTame v δT →
    ∀ [MeasurableSpace (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))] [BorelSpace (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))]
      (ν : Measure (Matrix (Fin (r + d)) (Fin (r + c)) (Cv v))), ν.IsAddLeftInvariant → ν {x | ∀ i j, Valued.v (x i j) ≤ 1} = 1 →
      (∫ y, ‖phiB v δT r d c y‖ ^ 2 ∂ν = (qV K v : ℝ) ^ (-((r * d : ℕ) : ℤ)) * GlobalTheory.CompanionTheory.QL.qE (qV K v) 1 r) ∧
      (IsRam v δT → IsBlockKernel v J δT ((qV K v : ℂ) ^ (-(((r : ℂ) + d) / 2))) fun g =>
        (∫ y, linAct v δS δT g 1 (phiB v δT r d c) y * star (phiB v δT r d c y) ∂ν) / ((∫ y, ‖phiB v δT r d c y‖ ^ 2 ∂ν : ℝ) : ℂ))

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FinZeta (projV embV Kv Gv)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsIdemOf IsProjAt rdA grpCo frCo)
open GlobalTheory.CompanionTheory.Ipf.Loc (FPl)

variable {D : D7}

def IsQChart {v : FPl D} (φ : SplitProj D v) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r c : ℕ)
    (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)) : Prop :=
  ∃ h : r + c = V.rank, ∀ g, (e g).1 = (grpCo φ V (frCo φ β) (embV V v g)).1.submatrix (Fin.cast h) (Fin.cast h)

def IsLocCh {v : FPl D} (φ : SplitProj D v) (χ : (AE D)ˣ →* Circle) (δ : (Cv v)ˣ →* ℂˣ) : Prop :=
  ∀ e, IsIdemOf φ e → ∀ x : (AE D)ˣ, (1 - e) * (x : AE D) = 1 - e → ∀ y : (Cv v)ˣ, (y : Cv v) = rdA φ (x : AE D) →
    ((δ y : ℂˣ) : ℂ) = (χ x : ℂ)

def IsBlockVectorAtSplitPrime (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (F : GA D V → ℂ) (B : Multiset ℂˣ) : Prop :=
  ∀ (v : FPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (c : ℕ) (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)), IsQChart φ V β r c e →
    ∀ δ, IsLocCh φ χ δ → ∀ J, IsPar v r c J →
      IsBlockVector v J δ ((GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ).comp ((embV V v).comp e.symm.toMonoidHom)) F B

def IsKerAt (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r N : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (c₀ : GA D V → ℂ) : Prop :=
  ∀ (v : FPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (c : ℕ) (e : Gv V v ≃* GL (Fin (r + c)) (Cv v)), IsQChart φ V β r c e →
    ∀ δ, IsLocCh φ χ δ → ∀ J, IsPar v r c J → ∃ κ, IsBlockKernel v J δ ((qV D.host.F v : ℂ) ^ (-((N : ℂ) / 2))) κ ∧
      ∀ g, projV V v g = 1 → ∀ x : Gv V v, c₀ (g * embV V v x) = κ (e x) * c₀ g

def IsQPlace (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∃ (φ : SplitProj D (PP.under (𝓞 D.host.F))) (c : ℕ) (e : Gv V (PP.under (𝓞 D.host.F)) ≃* GL (Fin (r + c)) (Cv (PP.under (𝓞 D.host.F))))
    (δ : (Cv (PP.under (𝓞 D.host.F)))ˣ →* ℂˣ), IsProjAt φ PP ∧ (∃ i, IsIdemOf φ i) ∧ IsQChart φ V β r c e ∧
      (∀ g, g ∈ Kv V _ ↔ e g ∈ KGL _ (r + c)) ∧ IsLocCh φ χ δ ∧ IsTame _ δ ∧ IsRam _ δ

end Adelic

end GlobalTheory.CompanionTheory.Ipf.Val

end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.TwistedFlags.DownChainSucc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

namespace GlobalTheory.CompanionTheory.Sep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def per (φ : Fn G (.core 0)) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  ∫ h in M.fd (.grid 0 0), φ (stabilizerEmbedding G.sp.dec0 h) * u h ∂M.ν (.grid 0 0)

structure IsCoreForm (i : ℕ) (φ : Fn G (.core i)) : Prop where
  cusp : GlobalTheory.Mem.Th.IsCuspForm W.θ (G.V (.core i)) φ
  listed : G.IsListed W.θ (.core i) φ
  level : ∀ k ∈ GfC (G.V (.core i)), Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i) → ∀ g, φ (g * k) = φ g

def IsCoreDatum (i : ℕ) (f : Sch G (.coreDown i)) : Prop :=
  ∃ (v f₀ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) (e : AE D) (κ : Cos (G.Λ (.core (i + 1))) (G.Λ (.core i)) G.modul)
    (P : PolF D (G.pT (.core i)).rank (G.pS (.core i)).rank),
    W.IsVac (.core i) v ∧ IsIdemSum e G.pl.W0 ∧
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) 1
      v (cosInd e κ) f₀ ∧ f = W.fock (.core i) f₀ P

def downChain (f : ∀ i, Sch G (.coreDown i)) (n : ℕ) : Fn G (.core n) → Fn G (.core 0) :=
  Nat.rec (motive := fun n => Fn G (.core n) → Fn G (.core 0)) (fun F => F)
    (fun n ih F => ih (liftA W M (.coreDown n) (f n) F)) n

def CoreHaar : Prop := ∀ i, i ≤ D.R.m → GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions.HaarAt M (.core i)

def HasPeriod (u : GA D (Yc D 0) → ℂ) : Prop := ∃ φ, IsCoreForm W 0 φ ∧ per M φ u ≠ 0

def HasColumn (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∃ Ψ ∈ Cols G W.θ, ∃ (ξ : Module.Dual ℂ (coefPlus G W.θ).W) (f : ∀ i, Sch G (.coreDown i)),
    (∀ i, i < D.R.m → IsCoreDatum W i (f i)) ∧ per M (downChain W M f D.R.m (pairVec (coefPlus G W.θ) ξ Ψ)) u ≠ 0

def HasValue (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∃ (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W), ∃ Ψ ∈ Cols G W.θ, ∃ Φ : G.Datum, fPsiPhi W M ρ ξ Ψ Φ u ≠ 0

end Objects

abbrev PropG := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
  {G : GridData R.toLevCh sc}, G.Weil → Vol G → Prop

def Big (P : PropG) : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    GlobalTheory.GLq.ESerTie D →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
      R.toLevCh.Is A.μ0 → R.grp_record →
      ∀ (G : GridData R.toLevCh ⟨1, CF, large₂.sc.b⟩) (W : G.Weil), W.Over R → ∀ M : Vol G, M.IsRow → P R W M

def Conv : Prop := Big fun R _ G W M => ∀ t ∈ R.EEat R.triv, ∀ (w : SmT (R.MY 0)) (ρ : G.RealVec)
  (ξ : Module.Dual ℂ (coefPlus G W.θ).W), ∀ Ψ ∈ Cols G W.θ, ∀ Φ : G.Datum, FConv W M ρ ξ Ψ Φ (rowForm R w t)

def RankOne : Prop := Big fun R _ G W M => ∀ (w : SmT (R.MY 0)) (ρ ρ' : G.RealVec)
  (ξ ξ' : Module.Dual ℂ (coefPlus G W.θ).W), ∀ t ∈ R.EEat R.triv, ∀ t' ∈ R.EEat R.triv, ∀ Ψ ∈ Cols G W.θ, ∀ Ψ' ∈ Cols G W.θ,
    ∀ Φ Φ' : G.Datum, fPsiPhi W M ρ ξ Ψ Φ (rowForm R w t) * fPsiPhi W M ρ' ξ' Ψ' Φ' (rowForm R w t') =
      fPsiPhi W M ρ ξ Ψ' Φ' (rowForm R w t') * fPsiPhi W M ρ' ξ' Ψ Φ (rowForm R w t)

def AllVec : Prop := Big fun R _ _ W M => ∀ t ∈ R.EEat R.triv, ∀ w₀ w : SmT (R.MY 0), w ≠ 0 →
  HasValue W M (rowForm R w₀ t) → HasValue W M (rowForm R w t)

def PerEx : Prop := Big fun R _ _ W M => ∀ t ∈ R.EEat R.triv, t ≠ 0 → ∃ w : SmT (R.MY 0), HasPeriod W M (rowForm R w t)

def Onto : Prop := Big fun R _ _ W M => CoreHaar M → ∀ t ∈ R.EEat R.triv, ∀ w : SmT (R.MY 0),
  HasPeriod W M (rowForm R w t) → HasColumn W M (rowForm R w t)

def Unfold : Prop := Big fun R _ _ W M => CoreHaar M → ∀ t ∈ R.EEat R.triv, ∀ w : SmT (R.MY 0),
  HasColumn W M (rowForm R w t) → HasValue W M (rowForm R w t)

def Rechoose : Prop := Big fun _ _ G _ M => ∃ M' : Vol G, CoreHaar M' ∧ M'.νN = M.νN ∧ M'.fdN = M.fdN ∧
  ∀ X : Node, (∀ i, X ≠ .core i) → M'.ν X = M.ν X ∧ M'.fd X = M.fd X

end GlobalTheory.CompanionTheory.Sep

end
end

