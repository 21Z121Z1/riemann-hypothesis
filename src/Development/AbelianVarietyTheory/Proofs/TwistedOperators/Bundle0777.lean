import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0772
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0773
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.DifferentiableConjConj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PPSemichar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0771
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0753

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiE_at_S0_column_pair : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  first | exact @GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | exact GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | (intros; apply GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingFundamentalDomainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_fundamental_domain : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ N : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @GlobalTheory.SquareAgree.exists_kerPD_thetaSub | exact GlobalTheory.SquareAgree.exists_kerPD_thetaSub | (intros; apply GlobalTheory.SquareAgree.exists_kerPD_thetaSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def ahG {W : UnfAt U k x} (Y : UnitAt W) (w : Fin W.g → ℂ) : ℂ :=
  Complex.exp (-(Real.pi / 2 * hermForm Y.Hm w w)) * Y.θ w

theorem ahG_add_period (W : UnfAt U k x) (Y : UnitAt W) (a : (W.F.Di (W.ik k)).La) (w : Fin W.g → ℂ) :
    ahG Y (w + W.Pm a) =
      Y.χl (W.Pm a) * Complex.exp (Real.pi * Complex.I * (hermForm Y.Hm w (W.Pm a)).im) * ahG Y w := by
  unfold ahG
  rw [theta_add W Y a w]
  have hs := hermForm_swap Y.herm w (W.Pm a)
  have hsc : hermForm Y.Hm w (W.Pm a) - star (hermForm Y.Hm w (W.Pm a)) =
      2 * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) * Complex.I := by
    rw [show star (hermForm Y.Hm w (W.Pm a)) = (starRingEnd ℂ) (hermForm Y.Hm w (W.Pm a)) from rfl, Complex.sub_conj]
    push_cast; ring
  have e : -(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)) +
      (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a)) =
      ↑Real.pi * Complex.I * ((hermForm Y.Hm w (W.Pm a)).im : ℂ) + -(↑Real.pi / 2 * hermForm Y.Hm w w) := by
    rw [hermForm_add_left, hermForm_add_right, hermForm_add_right, hs]
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  calc Complex.exp (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a))) *
        (Y.χl (W.Pm a) * Complex.exp (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a)) * Y.θ w)
      = Y.χl (W.Pm a) * Complex.exp (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)) +
        (↑Real.pi * hermForm Y.Hm w (W.Pm a) + ↑Real.pi / 2 * hermForm Y.Hm (W.Pm a) (W.Pm a))) * Y.θ w := by
        rw [Complex.exp_add (-(↑Real.pi / 2 * hermForm Y.Hm (w + W.Pm a) (w + W.Pm a)))]; ring
    _ = _ := by rw [e, Complex.exp_add]; ring

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
  {hV : T.V ((i : ℕ) + 1) σ = Wc D i}

def colB (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E)
    (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (a : Fin (Vc D i).rank) : Fin D.R.r → D.host.E :=
  fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a

def PinAt (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E)
    (γ g : GA D (Wc D i))
    (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
    (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt) : Prop :=
  ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
    (∀ a, z a = perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
    Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
        thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) (realPt (Vc D i) (Wc D i) X) =
      ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) * ∏ a, Y.θ (z a)

theorem thetaAt_eq_prod_ahG {ph : ℂ} {b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E} {γ g : GA D (Wc D i)}
    {hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom}
    {Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩} {Y : UnitAt Wt}
    (hp : PinAt T R i σ hV ph b γ g hx Wt Y) (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) :
    thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) (realPt (Vc D i) (Wc D i) X) =
      ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) *
        ∏ a, ahG Y (perVec Wt (colB b X a)) := by
  have h := hp X (fun a => perVec Wt (colB b X a)) fun a => rfl
  have hE : Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) ≠ 0 :=
    Complex.exp_ne_zero _
  apply mul_left_cancel₀ hE
  rw [h]
  simp only [ahG, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  have : Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a))) *
      Complex.exp (∑ a, -(Real.pi / 2 * hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b X a)))) = 1 := by
    rw [← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV g).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) g) *
    ∏ a, Y.θ (perVec Wt (colB b X a)))) * this

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def pv (W : UnfAt U k x) (v : Fin r → E) : Fin W.g → ℂ :=
  fun j => perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2

theorem perFr_add' (X : Data E r) (y : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X y (v + w) τ i = perFr X y v τ i + perFr X y w τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := fun ρ => by
    ext a; simp [Data.emb]
  unfold perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

def pvHom (W : UnfAt U k x) : (Fin r → E) →+ (Fin W.g → ℂ) :=
  AddMonoidHom.mk' (pv W) fun v w => funext fun j => perFr_add' _ _ _ _ _ _

theorem pv_nsmul (W : UnfAt U k x) (N : ℕ) (v : Fin r → E) : pv W ((N : E) • v) = (N : ℂ) • pv W v := by
  have h1 : (N : E) • v = N • v := by rw [Nat.cast_smul_eq_nsmul]
  have h2 : pv W (N • v) = N • pv W v := map_nsmul (pvHom W) N v
  rw [h1, h2, Nat.cast_smul_eq_nsmul]

theorem pv_lat (W : UnfAt U k x) (a : (W.F.Di (W.ik k)).La) : pv W (W.φ k a : Fin r → E) = W.Pm a :=
  funext fun j => (W.pm_eq a j).symm

theorem herm_nsmul (G : Matrix (Fin r) (Fin r) E) (N M : ℕ) (u v : Fin r → E) :
    herm G ((N : E) • u) ((M : E) • v) = (N : E) * M * herm G u v := by
  have hc : cc (M : E) = M := map_natCast _ M
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e2 : cc ((M : E) * v b) = (M : E) * cc (v b) := by
    simp only [cc, map_mul, map_natCast]
  rw [e2]; ring

theorem hermForm_nsmul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N M : ℕ) (z w : Fin g → ℂ) :
    hermForm Hm ((N : ℂ) • z) ((M : ℂ) • w) = (N : ℂ) * M * hermForm Hm z w := by
  rw [hermForm_smul_left, show ((M : ℂ) • w) = (((M : ℝ) : ℂ) • w) by norm_cast, hermForm_real_smul_right]
  push_cast; ring

theorem exists_nsmul_mem (X : Data E r) (u : Fin r → E) : ∃ N : ℕ, N ≠ 0 ∧ N • u ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem X u

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem im_hermForm_pv (W : UnfAt U k x) (Y : UnitAt W) (u v : Fin r → E) :
    (hermForm Y.Hm (pv W u) (pv W v)).im =
      ((Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) : ℚ) : ℝ) := by
  obtain ⟨N, hN, hu⟩ := exists_nsmul_mem (U.X k) u
  obtain ⟨M, hM, hv⟩ := exists_nsmul_mem (U.X k) v
  set a := (W.φ k).symm ⟨N • u, hu⟩ with ha
  set b := (W.φ k).symm ⟨M • v, hv⟩ with hb
  have hau : (W.φ k a : Fin r → E) = (N : E) • u := by
    rw [ha, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
  have hbv : (W.φ k b : Fin r → E) = (M : E) • v := by
    rw [hb, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
  have h1 := Y.c1 a b
  have h2 := W.isom k a b
  rw [← pv_lat, ← pv_lat, hau, hbv, pv_nsmul, pv_nsmul, hermForm_nsmul] at h1
  rw [hau, hbv, herm_nsmul] at h2
  have hNM : ((N : ℝ) * M) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hN) (Nat.cast_ne_zero.2 hM)
  have h3 : ((N : ℂ) * M * hermForm Y.Hm (pv W u) (pv W v)).im = (N : ℝ) * M * (hermForm Y.Hm (pv W u) (pv W v)).im := by
    rw [show ((N : ℂ) * M) = (((N : ℝ) * M : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have h4 : Algebra.trace ℚ E (-(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v)) =
      ((N : ℚ) * M) * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) := by
    have e : -(U.X k).ξ0 * ((N : E) * M * herm (U.X k).Gm u v) =
        (((N : ℚ) * M) : ℚ) • (-(U.X k).ξ0 * herm (U.X k).Gm u v) := by
      rw [Algebra.smul_def]; push_cast; ring
    rw [e, map_smul, smul_eq_mul]
  rw [h4] at h2
  have h5 : ((N : ℝ) * M) * (hermForm Y.Hm (pv W u) (pv W v)).im =
      ((N : ℝ) * M) * ((Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm u v) : ℚ) : ℝ) := by
    rw [← h3, h1]
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
    exact this
  exact mul_left_cancel₀ hNM h5

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.FinTranslate

variable {D : D7}

theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

theorem realPt_add (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    realPt S T (X + Y) = realPt S T X + realPt S T Y := by
  ext i j
  simp only [realPt, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]

theorem theta_realPt_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    f (realPt S T (X + Y)) = ψ (symplOH S T (realPt S T X) (realPt S T Y)) *
      heisO ψ S T (-(ratW T S Y - realPt S T Y)) f (realPt S T X) := by
  set y := ratW T S Y - realPt S T Y with hy
  have hy0 : y.map (infPart D) = 0 := GlobalTheory.HeisRatRead.ratW_sub_realPt_inf S T Y
  have hX0 : (realPt S T X).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin S T X
  have hY0 : (realPt S T Y).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin S T Y
  have hpt : realPt S T (X + Y) = ratW T S Y + (realPt S T X - y) := by
    rw [realPt_add, hy]; abel
  have hrat : ratW T S Y = realPt S T Y + y := by rw [hy]; abel
  rw [hpt, hf.quasi]
  simp only [heisO]
  rw [sub_eq_add_neg (realPt S T X) y, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hrat, symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_neg_right, symplOH_neg_right,
    symplOH_neg_right, symplOH_self, symplOH_real_fin hy0 hY0, symplOH_fin_real hy0 hX0, symplOH_real_fin hy0 hX0,
    symplOH_skew (S := S) (T := T) (realPt S T X) (realPt S T Y)]
  ring

end GlobalTheory.AHPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SphOffFinite

theorem vac_unique_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hs hψv h2 θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.T.splitPlace_tensorLattice_selfDual F E σ B hTr.base G.V' G.W _ _ _ _ hTr.geo.hV' hTr.geo.hW v hs hψv z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat hTr.geo.hW.lat
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf
    (fun u hu => ?_) φ (G.M'.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM'.vac v).1 hvac) (hTr.geo.hM'.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

theorem isUnram_of_unramified {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  intro P hP
  rw [Ideal.ramificationIdx_eq_one_iff]
  infer_instance

theorem vac_fixed_off_finite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F |
      ¬ G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM'.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (isUnram_of_unramified hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
    have h1 := GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB φ₁ hφ₁ hact hvac
    obtain ⟨c, rfl⟩ := vac_unique_split hPr F E σ B a a' G X om om' hTr v hs hψ h2 θ hθ hvac φ₁ hφ₁ h1
    have hc := GlobalTheory.T.vacuum_split_place_indicator hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum F E σ B a a' G X om om' hTr v w hw hvT k hk

end GlobalTheory.SphOffFinite
end
end

