import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SphericalEisensteinConvergence
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure ArchSec (Z : Comp Xo c) (la : Weight Dw) : Type where

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exOf Dw la 0)
  inv_mem : inv ∈ secZ Xo c (-exOf Dw la 0)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, homN (U (goodOf c σ)) x (wtOf Dw la 0) sig '' framesOn (U (goodOf c σ)) Z = {cInf σ}

variable {U x} in

def ArchSec.ofConst {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) :
    ArchSec U x Z la :=
  ⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf⟩

example (Z : Comp Xo c) (h : HasPts U Z) : Nonempty (ArchSec U x Z 0) := ⟨.ofConst (ConstSec.one x h)⟩

def Onto : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) →
    4 * (finrank ℚ E * r) + 4 ≤ n →
    holSub0 (U σ).X (laU (U σ) a n) ≤ Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U a n : Set (Rul Xo c)))

structure Laws : Prop where
  pos : 1 ≤ Dw.p + Dw.q
  lev : l.A = 1
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  geo : FnAlgClosed Xo c
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x
  chi : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  det : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1
  onto : Onto U
  line : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0

def IsFlatQuot (Z : Comp Xo c) (τ : Psi H) (f g : Rul Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∃ a : ℂ, a ≠ 0 ∧ ∀ k (hτ : relab c σ τ.1 ∈ ((U σ).X k).Ψ) y,
    (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      rdU (U σ) g k y = a * horizGen ⟨_, hτ⟩ y * rdU (U σ) f k y

def htValAt (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) :
    Set (Rul Xo c → EReal) :=
  {w | ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
    (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y ∧
      w = fun f => val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (evR Xo c f y)}

def htValOn (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  {w | ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y₀ : IntFr Xo c T io),
    OverLa la T.V io e ∧ algOn Z T io y₀ ∧ w ∈ htValAt la y₀}

theorem htValOn_subset (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : htValOn Z la ⊆ htValSet Xo c la := by
  rintro w ⟨T, io, e, y₀, ho, hz, p, hp, ha, k, y, hy, rfl⟩
  exact ⟨p, hp, ha, T, io, e, y₀, k, y, ho, hz.1, hy, rfl⟩

def Always (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}, (∀ σ : c.F →+* ℂ, Unf Xo c σ r) → ℝ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → Q U x

def ArchEx : Prop := ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ))

def HTConst : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
    ∃ ρ : ℝ, ∀ w ∈ htValOn Z la, w s.sig = (ρ : EReal)

variable (Xo c) in

def HTShift : Prop :=
  ∀ (τ : Psi H) (la : HeightOneSpectrum (𝓞 c.F)), ∃ κ : ℝ,
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y₀ : IntFr Xo c T io), OverLa la T.V io e → y₀.IsAlg →
      ∀ w ∈ htValAt la y₀, ∀ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0), w f = nval T.V e (evI y₀ f) + (κ : EReal)

def FinConst : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
    ∃ ρ : ℝ, ∀ w ∈ valOn Z la, w s.sig = (ρ : EReal)

def FrameDeg (logOm : ℝ) : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ),
    (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) →
      (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ((Dw.p : ℝ) - Dw.q) / 2 * logOm

def CMDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CM.CMObj H K ρ σ₁ p q)
      (F : CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h →
      ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
        ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) -
            ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) =
          ((p : ℝ) - q) / 2 * (CM.logOm E χ).re

def FlatDegreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
      Laws U x → FlatDegree U x (CM.logOm E χ).re

end GlobalTheory.FlatCore

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ}

structure Fr (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  herm₀ : IsHermND σ J₀
  cc : cT (σ : E →+* E) C * J * C = 0
  dd : cT (σ : E →+* E) D * J * D = 0
  cd : cT (σ : E →+* E) C * J * D = 1
  dc : cT (σ : E →+* E) D * J * C = 1
  cz : cT (σ : E →+* E) C * J * Z = 0
  dz : cT (σ : E →+* E) D * J * Z = 0
  zc : cT (σ : E →+* E) Z * J * C = 0
  zd : cT (σ : E →+* E) Z * J * D = 0
  zz : cT (σ : E →+* E) Z * J * Z = J₀
  sum : C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J) = 1
  dim : m + 2 * j = n

def fixG {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) where
  carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change _ * _ = _ at ha hb ⊢
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, ha]
  inv_mem' := fun {a} ha => by
    change _ * _ = _ at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

structure IsLv (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J) : Prop where
  cont : Continuous lv
  onC : ∀ α, (matHom _ σ J (lv α)).1 * adMat F C = adMat F C * α.1
  onD : ∀ α, (matHom _ σ J (lv α)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1
  onZ : ∀ α, (matHom _ σ J (lv α)).1 * adMat F Z = adMat F Z
  rat : ∀ δ : GL (Fin j) E, lv (bc (inclR (F := F) (AF F)) δ) ∈ ratPts σ J

def plus (J₀ : Matrix (Fin m) (Fin m) E) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) : Matrix (Fin m) (Fin j) (AF F ⊗[F] E) :=
  adMat F J₀⁻¹ * cT (sigR (AF F) σ) b

structure Crd (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) (u : GAd σ J)
    (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) : Prop where
  onC : (matHom _ σ J u).1 * adMat F C = adMat F C
  onZ : (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b
  onD : (matHom _ σ J u).1 * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c

variable (F E) in

abbrev tor (l : Fin j → ℤ) : GL (Fin j) (AF F ⊗[F] E) := GlobalTheory.Eis.Conv.dg (GlobalTheory.Eis.Conv.halfE F E) l

variable (F) in

abbrev bse : ℝ := 4 ^ Fintype.card (InfinitePlace F)

example (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) :
    Crd σ J C D Z J₀ 1 0 0 := ⟨by simp, by simp, by simp [plus, cT]⟩

example (h : IsCMExt F E σ) : Fr σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) !![0; 1]
    (0 : Matrix (Fin 2) (Fin 0) E) 1 := by
  refine ⟨h, ⟨fun i j => ?_, by simp⟩, ⟨fun i => i.elim0, by simp⟩, ?_, ?_, ?_, ?_, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_, rfl⟩
  · fin_cases i <;> fin_cases j <;> simp
  all_goals ext i j; fin_cases i <;> fin_cases j <;> simp [cT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid

namespace GlobalTheory.FunObj.SqNum.Model

variable (D : D7)

theorem e_add_v (τ : D.what₂.Tau) (j : Fin D.R.m) :
    0 < (D.hc τ).e j + (D.hc τ).v ⟨0, by have := D.R.m_add_three_le_k; omega⟩ := by
  set P := D.hc τ
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h1 : ∀ a (h : a < D.R.m), P.b ⟨0, by omega⟩ ≤ P.b ⟨a, h⟩ := by
    intro a; induction a with
    | zero => intro _; exact le_rfl
    | succ a ih =>
      intro h; have := ih (by omega); have := P.gap_be ⟨a, by omega⟩; have := P.gap_eb ⟨a, by omega⟩ h
      simp only at *; linarith
  have h2 : ∀ a (h : a < D.R.k - 1), P.u ⟨a + 1, by omega⟩ < P.v ⟨0, by omega⟩ := by
    intro a; induction a with
    | zero => intro h; exact P.v_gt_u ⟨0, h⟩
    | succ a ih =>
      intro h; have := ih (by omega); have := P.v_gt_u ⟨a + 1, h⟩; have := P.u_gt_v ⟨a + 1, h⟩
      simp only at *; linarith
  have h3 := P.u_last_gt (by omega) (by omega)
  have h4 := h2 (D.R.k - 2) (by omega)
  have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
  rw [e] at h4
  have h5 := h1 j.1 j.2
  have h6 := P.gap_be j
  simp only [Fin.eta] at h5
  linarith

theorem gap_le (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    (gap D C : ℤ) ≤ (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) := by
  have h := e_add_v D τ j
  have s := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  have s0 := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) 0
  rw [s.2.2, s0.1] at h
  rw [← sub_le_iff_le_add', cen, Int.le_floor]
  simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a]
  have hi := i.2
  have e1 : ((D.R.m - i - 1 : ℕ) : ℚ) = D.R.m - i - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have e2 : ((D.R.m - i : ℕ) : ℚ) = D.R.m - i := by rw [Nat.cast_sub (by omega)]
  rw [e1, e2]
  have g0 : (0 : ℚ) ≤ gap D C := by positivity
  have i0 : (0 : ℚ) ≤ (i : ℕ) := by positivity
  have := mul_nonneg g0 i0
  change _ ≤ (_ + 1 / 2 + ((D.R.m : ℚ) + 1 - _) * (gap D C : ℚ) +
    (_ + 1 / 2 + ((D.R.m : ℚ) + 1 - _) * (gap D C : ℚ))) / 2
  simp only [zero_add] at h
  push_cast
  unfold num
  nlinarith

theorem kap_add (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ halfRank D i j) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := gap_le D C i j τ
  have h2 := (isLeast_gap D C).1.2.1
  have h3 : halfRank D i j ≤ bigN D := by
    have a : rankV D (i + 1) (j + 1) ≤ bigN D := by
      have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
      have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
      simp only [rankV, bigN, Ranks.r, mul_add] at *
      omega
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    unfold halfRank; omega
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

variable {D} {T : Type} {L : LevCh D T} {sc : Consts}

open Classical in

theorem expIn_condF (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.CMVal.expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    obtain ⟨u, hu, h⟩ := (v.prime.dvd_finset_prod_iff _).1 h
    have h2 := v.prime.dvd_of_dvd_pow h
    have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
    exact hS (this ▸ hu)
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero.2 (key _ h)

theorem levelLe_mono {χ : HChar D.host.E} {v : HeightOneSpectrum (𝓞 D.host.E)} {m n : ℕ} (h : χ.LevelLe v m)
    (hmn : m ≤ n) : χ.LevelLe v n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_div (G : GridData L sc) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) {θ : HChar D.host.E} (ht : ∀ P, θ.TameAt P)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → θ.UnrAt P)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.CMVal.ExpAt (θ / G.ch.chiH k) P (GlobalTheory.CMVal.expIn (condF G.pl) (P.under (𝓞 D.host.F))) := by
  have back : ∀ n, θ.LevelLe P n → (θ / G.ch.chiH k).LevelLe P n → (G.ch.chiH k).LevelLe P n := fun n a b => by
    have := a.mul b.inv
    rwa [inv_div, mul_div_cancel] at this
  have fwd : ∀ n, θ.LevelLe P n → (G.ch.chiH k).LevelLe P n → (θ / G.ch.chiH k).LevelLe P n := fun n a b => by
    rw [div_eq_mul_inv]; exact a.mul b.inv
  rw [expIn_condF]
  intro n
  split_ifs with h
  · by_cases e : P.under (𝓞 D.host.F) = G.pl.v0
    · have l := G.ch.lev0 k h1 h2 P e
      have u := hu P (e ▸ G.ch.basePlace_not_mem_chiGridBadPlaces)
      rw [condExp, if_pos e]
      refine ⟨fun hn => ?_, fun hn => levelLe_mono (fwd 1 (ht P) l.1) hn⟩
      by_contra c
      obtain rfl : n = 0 := by omega
      exact l.2 ((HChar.unrAt_iff _ _).2 (back 0 (u.levelLe 0) hn))
    · have l := G.ch.lev1 k h1 h2 P ((G.pl.mem_S0_of_sum_eq.1 h).resolve_left e)
      rw [condExp, if_neg e]
      refine ⟨fun hn => ?_, fun hn => levelLe_mono (fwd 2 (levelLe_mono (ht P) (by omega)) l.1) hn⟩
      by_contra c
      exact l.2 (back 1 (ht P) (levelLe_mono hn (by omega)))
  · refine ⟨fun _ => Nat.zero_le _, fun _ => fwd n ((hu P fun c => h (G.pl.mem_S0_of_sum_eq.2 (Or.inr c))).levelLe n)
      ((G.ch.unr k h1 h2 P h).levelLe n)⟩

theorem isValChar_twist {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j)
    {ξ : HChar D.host.E} (hf : ∃ n, 0 < n ∧ ξ.OrderDvd n) (htr : ξ.TrivOn D.host.F) (ht : ∀ P, ξ.TameAt P)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → ξ.UnrAt P) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j * ξ) := by
  obtain ⟨n, hn, hf⟩ := hf
  have hm := L.C.isMu0 j
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have e : nuH G μ₀ i j * ξ = L.C.mu0 j * ξ / G.ch.chiH (D.R.m - i) := by
    rw [nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]
  refine ⟨(GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)).mul (HChar.isUnitary_of_order hn hf), ?_, ?_,
    fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty _), fun _ => ?_⟩⟩
  · rw [e, div_eq_mul_inv]
    exact (hm.triv.mul htr).mul (G.ch.triv _ a1 a2).inv
  · intro k
    obtain ⟨n', hn', hinf⟩ := hm.inf
    have hk : ∀ τ, embTau D τ (k : D.host.E) ≠ 0 := fun τ => by simp
    rw [e, div_eq_mul_inv, HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, GlobalTheory.TypeValues.inf_eq_one ξ hn hf, mul_one,
      Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1)) := by
      have := hn' (D.eTau τ)
      beta_reduce at this
      rw [Formalism.L2.Host.eExp, Equiv.symm_apply_apply,
        (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2] at this
      have h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ) := by
        rw [this]; push_cast; unfold num; ring
      exact_mod_cast h2
    beta_reduce
    rw [h1, (kap_add D sc.cGap i j τ hs).1]
    have hz : (cmPhi D τ (k : D.host.E) / ((‖cmPhi D τ (k : D.host.E)‖ : ℝ) : ℂ)) =
        (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ))⁻¹ := by
      have : cmPhi D τ (k : D.host.E) = starRingEnd ℂ (embTau D τ (k : D.host.E)) := rfl
      rw [this, RCLike.norm_conj, inv_div, div_eq_div_iff (by simpa using hk τ) (hk τ), Complex.conj_mul']
      ring
    have hne : (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0 :=
      div_ne_zero (hk τ) (by simpa using hk τ)
    rw [hz, inv_zpow', ← zpow_neg]
    change (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _ = _
    rw [← zpow_add₀ hne]
    congr 1
    ring
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    rw [e]
    refine expAt_div G a1 a2 (fun Q => HChar.LevelLe.mul (hm.tame Q) (ht Q)) (fun Q hQ => HChar.UnrAt.mul
      (hm.unr Q fun k hk => hQ ((S1_mem_OmF D).2 ?_)) (hu Q hQ)) P
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

theorem isValChar_nu {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) ∧
      ∀ c, GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j * delOf L c) := by
  have up : ∀ (p : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.Host.OverP D.host p Q →
      ((p : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := fun p Q h => by
    show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]; exact h
  refine ⟨?_, fun c => ?_⟩
  · simpa using isValChar_twist hL G i j hs (ξ := 1) ⟨1, one_pos, one_pow 1⟩ (hL.xi_base ▸ hL.xi_triv μ₀)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  · cases c
    · have h := L.C.isDel
      exact isValChar_twist hL G i j hs h.fin h.triv h.tame fun Q hQ => h.unr Q fun o =>
        hQ ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl (up _ Q o)))))
    · have h := L.C.isDel'
      exact isValChar_twist hL G i j hs h.fin h.triv h.tame fun Q hQ => h.unr Q fun o =>
        hQ ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr (up _ Q o)))))

theorem gauge_unique {G : GridData L sc} {t : T} {i j : Fin D.R.m} {s : ℕ} {zd zd' g g'} (h : IsTorVal G t i j s zd g)
    (h' : IsTorVal G t i j s zd' g') : g = g' := by
  obtain ⟨x, h1, -, -, Λ, p, hΛ, hp, hg⟩ := h
  obtain ⟨x', h1', -, -, Λ', p', hΛ', hp', hg'⟩ := h'
  obtain rfl := h1.2.unique h1'.2
  have e : Λ.lattice = Λ'.lattice := Submodule.ext fun y => (hΛ y).trans (hΛ' y).symm
  have e2 : GlobalTheory.CMVal.latDisc Λ = GlobalTheory.CMVal.latDisc Λ' := by
    simp only [GlobalTheory.CMVal.latDisc, PeriodPair.g₂, PeriodPair.g₃, PeriodPair.G]
    rw [e]
  have e3 : p = p' := by
    rw [hp.eq_minpoly, hp'.eq_minpoly, GlobalTheory.CMVal.beta, GlobalTheory.CMVal.beta, e2]
  exact funext fun w => by rw [hg, hg', e3]

theorem bot_ranks (i j : Fin D.R.m) : 2 ≤ botSmall D i j ∧ botSmall D i j < botBig D i j ∧
    Even (botBig D i j + botSmall D i j) ∧ botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have a : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
    have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
    simp only [rankV, bigN, Ranks.r, mul_add] at *
    omega
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 := D.R.m_add_three_le_k
  have h6 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h7 : sLen D = D.R.r + 6 := rfl
  refine ⟨by omega, by omega, Nat.even_iff.2 (by omega), by omega⟩

end GlobalTheory.FunObj.SqNum.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResidueEisenstein

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ScalesBy (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (p : GAd σ J)
    (β : GL (Fin k) (AF F ⊗[F] E)) : Prop := (matHom _ σ J p).1 * adMat F X = adMat F X * β.1

structure DataJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  lat : Submodule.IsLattice E L
  iwa : ∀ g, ∃ p β, ScalesBy σ J X p β ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p β, ScalesBy σ J X p β → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)

def IsRepsJ (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (T : Set (ratPts σ J)) :
    Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ β, ScalesBy σ J X (γ * t⁻¹ : ratPts σ J).1 β

structure IsFlowJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (b : ℝ → GAd σ J) : Prop where
  cont : Continuous b
  add : ∀ s t, b (s + t) = b s * b t
  onX : ∀ t, ∃ β, ScalesBy σ J X (b t) β ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) = Real.exp t
  mem : ∀ t, b t ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, b t * m = m * b t

example (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) : ScalesBy σ J X 1 1 := by
  simp [ScalesBy]

end GlobalTheory.ResidueEisenstein

end
end

