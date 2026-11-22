import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Mu0ChiHUnramifiedOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistUnr

theorem mu0_chiH_unrAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Lc.Q t → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (Lc.C.mu0 j).UnrAt w ∧ (G.ch.chiH (D.R.m - i)).UnrAt w := by
  intro D T Lc sc G μ₀ hL i j t w hw hS
  refine ⟨?_, ?_⟩
  · refine Formalism.L2.Host.IsMu0.unr (Lc.C.isMu0 j) w ?_
    intro k hmemE
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t w hw
    haveI : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    have : w.asIdeal.IsPrime := w.isPrime
    haveI : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
    have h0g : ((D.host.g k : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).2 hmemE
      simpa using this
    have h0q : ((q : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP w)
    have hd1 : ringChar (Formalism.L2.DIV.kP w) ∣ D.host.g k := ringChar.dvd h0g
    have hd2 : ringChar (Formalism.L2.DIV.kP w) ∣ q := ringChar.dvd h0q
    have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
    have h1 : ringChar (Formalism.L2.DIV.kP w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
    exact CharP.ringChar_ne_one h1
  · have hi := i.isLt
    exact G.ch.unr (D.R.m - (i : ℕ)) (by omega) (Nat.sub_le _ _) w hS

end GlobalTheory.TwistUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfOrth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower.TopExists

section Sum

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.AdelicU Matrix

theorem negIdx_of_orth {D : D7} {V₁ V₂ WW : HSp D} {p q : ℕ} (hr : V₁.rank + V₂.rank = WW.rank)
    (ι₁ : V₁.V →ₗ[D.host.E] WW.V) (ι₂ : V₂.V →ₗ[D.host.E] WW.V) (e₁ : Formalism.BasicNotions.HSpace.IsIsomEmb V₁ WW ι₁)
    (e₂ : Formalism.BasicNotions.HSpace.IsIsomEmb V₂ WW ι₂) (ho : ∀ x y, WW.hD (ι₁ x) (ι₂ y) = 0) (h1 : NegIdx V₁ p)
    (h2 : NegIdx V₂ q) : NegIdx WW (p + q) := by
  intro τ
  have c1 := (Formalism.UG.P.sig_data _ _ _ (h1 τ)).1
  have c2 := (Formalism.UG.P.sig_data _ _ _ (h2 τ)).1
  simp only [Fintype.card_fin] at c1 c2
  let v : Fin V₁.rank ⊕ Fin V₂.rank → WW.V :=
    Sum.elim (fun i => ι₁ (V₁.frame i)) (fun j => ι₂ (V₂.frame j))
  have hv : (Matrix.of fun k l => WW.hT (v k) (v l)) = fromBlocks V₁.gram 0 0 V₂.gram := by
    ext (i | i) (j | j)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Sum.elim_inl]; exact e₁ _ _
    · have h := WW.herm.eq (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i))
      have h0 : WW.hT (ι₂ (V₂.frame j)) (ι₁ (V₁.frame i)) = 0 := ho _ _
      rw [h0, map_zero] at h
      simp [v, ← h]
    · simp only [v, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
      exact ho (V₁.frame j) (V₂.frame i)
    · simp only [v, HSpace.gram, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Sum.elim_inr]; exact e₂ _ _
  have key := (GlobalTheory.SumSig.gram_family WW v).symm.trans hv
  set C := Matrix.of fun i k => WW.frame.repr (v k) i
  have hst : Function.Semiconj (tauE D τ) star star := fun a => D.sp.cm.cmUnram.2.1 _ a
  have hmap : (C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ) =
      fromBlocks (gramAt D V₁ τ) 0 0 (gramAt D V₂ τ) := by
    have := congrArg (fun M => M.map (tauE D τ)) key
    simp only [Matrix.map_mul, Matrix.conjTranspose_map _ hst, Matrix.fromBlocks_map, map_zero] at this
    simpa [gramAt] using this
  have hF := GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 τ) (h2 τ)
  obtain ⟨-, Q0, hQ0⟩ := Formalism.UG.P.sig_data _ _ _ hF
  have e : WW.rank - (p + q) = (V₁.rank - p) + (V₂.rank - q) := by omega
  rw [e]
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp; omega) (C.map (tauE D τ) * Q0) ?_
  calc (C.map (tauE D τ) * Q0)ᴴ * gramAt D WW τ * (C.map (tauE D τ) * Q0)
        = Q0ᴴ * ((C.map (tauE D τ))ᴴ * gramAt D WW τ * C.map (tauE D τ)) * Q0 := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hmap, hQ0]

end Sum

section Idem

open Formalism.IndefR.Lev in

theorem idem_exists {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (t : T) : ∃ e : AE D, IsIdemSum e (locPl G t) := by
  classical
  obtain ⟨e0, he0, -⟩ := W.cosVec_is
  have hW := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0
  have hQ := hL.Q_pl t
  have key : ∀ P ∈ Lc.Q t, ∀ P' ∈ G.pl.W0, (IsConjPl P P' ∨ IsConjPl P' P) → P ∈ G.pl.W0 := by
    intro P hPQ P' hP' hc
    have hu : P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
      rcases hc with hc | hc
      · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      · exact (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).symm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP'
    rw [G.pl.under_w hv] at hu
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact absurd hu (G.pl.levelPlace_ne_basePlace t P hPQ)
    · rw [G.pl.w_Q t P hPQ (hu ▸ h1), hu]
      exact Finset.mem_image_of_mem _ hv
  have hnc : ∀ P ∈ locPl G t, ∀ P' ∈ locPl G t, ¬ IsConjPl P P' := by
    intro P hP1 P' hP2 hc
    simp only [locPl, Finset.mem_union] at hP1 hP2
    rcases hP1 with h1 | h1 <;> rcases hP2 with h2 | h2
    · exact hW P h1 P' h2 hc
    · exact hW P h1 P' (key P' h2 P h1 (Or.inr hc)) hc
    · exact hW P (key P h1 P' h2 (Or.inl hc)) P' h2 hc
    · exact (hQ P h1).2 P' h2 hc
  let es : Formalism.L2.DIV.Pl D.host.E → AE D := fun PP =>
    if h : ¬ IsConjPl PP PP then (Formalism.IndefR.Fin.idem_exists_at PP h).choose else 0
  have hes : ∀ PP ∈ locPl G t, Formalism.L2.NTheta.IsIdemAt (es PP) PP := by
    intro PP hPP
    have h := hnc PP hPP PP hPP
    simp only [es, dif_pos h]
    exact (Formalism.IndefR.Fin.idem_exists_at PP h).choose_spec.1
  refine ⟨∑ PP ∈ locPl G t, es PP, ⟨es, hes, rfl⟩, ?_⟩
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => Finset.sum_eq_zero fun PP' hPP' => ?_
  exact Formalism.IndefR.Fin.idem_orth_conj (hnc PP hPP PP hPP) (hes PP hPP) (hes PP' hPP') (hnc PP hPP PP' hPP')

end Idem

section Chars

open GlobalTheory.HeckeCharsOfSquare

theorem chars {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}
    (hL : Lc.Is μ₀) (W : G.Weil) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
    IsHeckeChar D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧
    IsHeckeChar D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) ∧
    ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) ∧
    ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) / (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)))
      (rankV D (i + 1) (j + 1) + rankV D i j) := by
  have ht : Odd D.R.t := D.R.t_odd
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  have hs : Odd (sLen D) := hr.add_even (by decide : Even 6)
  have hi := i.2
  have hj := j.2
  have rk : ∀ a b : ℕ, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b := fun a b ha hb =>
    (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hth : ResEta D (Lc.mu t (j + 1)) 0 ∧ ResEta D Lc.eta 1 := by
    have hW := W.om_is (.mu t i j) (show Node.InRange D.R.m (.grid i (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.mu t i j)).rank = rankV D i j := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.mu t i j)).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_
    have e3 : rankV D i (j + 1) = rankV D i j + D.R.t := by simp only [rankV]; ring
    rw [e3, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ ht
  have hdn : ResEta D (G.ch.chi (D.R.m - i)) 0 := by
    have hW := W.om_is (.chi i (j + 1)) (show Node.InRange D.R.m (.grid (i + 1) (j + 1)) from ⟨by omega, by omega⟩)
    have hS := hW.resS
    have hT := hW.resT
    have e1 : (G.pS (.chi i (j + 1))).rank = rankV D (i + 1) (j + 1) := rk _ _ (by omega) (by omega)
    have e2 : (G.pT (.chi i (j + 1))).rank = rankV D i (j + 1) := rk _ _ (by omega) (by omega)
    rw [GridData.chrS, e1] at hS
    rw [GridData.chrT, e2] at hT
    refine (GlobalTheory.HeckeCharsOfSquare.resEta_of_att hS hT ?_).1
    have e3 : rankV D (i + 1) (j + 1) = rankV D i (j + 1) + sLen D := by simp only [rankV]; ring
    rw [e3, add_comm, ← add_assoc]
    exact Even.add_odd ⟨_, rfl⟩ hs
  have hη : IsHeckeChar D Lc.eta := hL.eta.1
  have hμ : IsHeckeChar D (Lc.mu t (j + 1)) := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (hL.mu0 j).1 (hL.xi t).1
  have hχ : IsHeckeChar D (G.ch.chi (D.R.m - i)) := (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)).1
  have hα := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hμ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have hβ := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul hχ (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_pow hη (rankV D i j % 2))
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hs
  have rα : ResEta D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (rankV D i j) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hth.1 (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  have rβ : ResEta D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (rankV D (i + 1) (j + 1)) :=
    GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_mul hdn (GlobalTheory.HeckeCharsOfSquare.resEta_pow hth.2 (rankV D i j % 2))) (by omega)
  refine ⟨hα, hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hα hβ, GlobalTheory.HeckeCharsOfSquare.isHeckeChar_div hβ hα, rα, rβ, ?_, GlobalTheory.HeckeCharsOfSquare.resEta_div rβ rα⟩
  exact GlobalTheory.HeckeCharsOfSquare.resEta_of_mod (GlobalTheory.HeckeCharsOfSquare.resEta_div rα rβ) (by omega)

end Chars

end GlobalTheory.SqTower.TopExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_one_nonneg {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (v : VV ℂ lam) :
    0 ≤ nrm lam (fun _ => 1) v := by
  by_cases hv : v = 0
  · simp [nrm, hv]
  · exact (Complex.le_def.1 (GlobalTheory.CoefModel.pairK_pos lam (fun _ => Matrix.PosDef.one) v hv).le).1

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatRowAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)), ∀ u,
    ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjRowAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m))),
    (∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ),
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialHeckeLFunction_square_eq_primitive : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  first | exact @GlobalTheory.SqStep.charL_chs_eq | exact GlobalTheory.SqStep.charL_chs_eq | (intros; apply GlobalTheory.SqStep.charL_chs_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C, hC⟩ := hT μ₂ inferInstance

  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : (κ ⊕ κ' → AF F) ≃ₜ+ (κ → AF F) × (κ' → AF F) :=
    { e.toEquiv with
      map_add' := fun _ _ => rfl
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  haveI : (μ.map eA).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ eA
  set c := (μ.map eA).addHaarScalarFactor (μ₁.prod μ₂)
  have hprod : μ.map eA = c • μ₁.prod μ₂ := Measure.isAddLeftInvariant_eq_smul _ _

  have key : ∀ g : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable g →
      ∫⁻ z, g z ∂μ = c * ∫⁻ a, ∫⁻ b, g (Sum.elim a b) ∂μ₂ ∂μ₁ := by
    intro g hg
    have h1 : ∫⁻ z, g z ∂μ = ∫⁻ p, g (e.symm p) ∂(μ.map eA) := by
      rw [show μ.map eA = μ.map e.toMeasurableEquiv from rfl, lintegral_map_equiv]
      refine lintegral_congr fun z => ?_
      exact congrArg g (e.symm_apply_apply z).symm
    rw [h1, hprod, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
      lintegral_prod (fun p => g (e.symm p)) (hg.comp e.symm.continuous.measurable).aemeasurable]
    rfl
  have hmeas : ∀ Φ ∈ schA F (κ ⊕ κ'), Measurable fun z => ‖Φ z‖ₑ ^ 2 := fun Φ hΦ =>
    ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ).measurable.enorm).pow_const 2
  refine ⟨C, fun Φ hΦ => ?_⟩
  have hslice : ∀ a : κ → AF F, (fun x => Φ (Sum.elim a x)) ∈ schA F κ' := fun a =>
    GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ
  have hin : ∀ a : κ → AF F, ∫⁻ b, ‖partR T Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ =
      C * ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ := fun a => hC _ (hslice a)
  have hm2 : Measurable fun a : κ → AF F => ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ :=
    ((hmeas Φ hΦ).comp e.symm.continuous.measurable).lintegral_prod_right'
  rw [key _ (hmeas _ (hmem Φ hΦ)), key _ (hmeas Φ hΦ)]
  simp_rw [hin]
  rw [lintegral_const_mul _ hm2, mul_left_comm]

end GlobalTheory.DblEval.L2RightPartial

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmeticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeValuation_localDegree_arithmetic : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  first | exact @GlobalTheory.vw_lw_arith | exact GlobalTheory.vw_lw_arith | (intros; apply GlobalTheory.vw_lw_arith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumThetaStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (n g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), Even n → IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, C ≠ 0 ∧ ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → (∃ ϑ, GenReads U k bas idx e x ϑ) ∧ ∀ ϑ, GenReads U k bas idx e x ϑ → IsTheta1 (U.X k) bas idx (H.w0 : E) x.1 (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ ∧ ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  first | exact @GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | exact GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | (intros; apply GlobalTheory.AdTh.prod_gen_eq_const_mul_thA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemSB
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.FinPull

theorem pullback_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ w)) ∈
        SB (ι → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ ι κ _ _ D hD g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  set A := algebraMap F (FiniteAdeleRing (𝓞 F) F)
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact hD z (by simpa using hz)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D) (LinearMap.ker_eq_bot.mpr hinj)
  set L := LinearMap.toMatrix' G
  have hLD : L * D = 1 := by
    have : LinearMap.toMatrix' (G ∘ₗ Matrix.toLin' D) = LinearMap.toMatrix' LinearMap.id := by rw [hG]
    simpa [L, LinearMap.toMatrix'_comp] using this
  have hM : Continuous fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hN : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Function.LeftInverse (fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w)
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w) := fun w => by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hLD, Matrix.map_one A (map_zero A) (map_one A), Matrix.one_mulVec]
  exact ⟨hg.1.comp_continuous hM, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding hN hM)⟩

end GlobalTheory.FinPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsSelfAnnihilatorSymplecticStandardCStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_self_annihilator_symplectic_standardChar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  first | exact @GlobalTheory.RatAnnihF.ratLF_annihilator | exact GlobalTheory.RatAnnihF.ratLF_annihilator | (intros; apply GlobalTheory.RatAnnihF.ratLF_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectorsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  first | exact @GlobalTheory.ThetaShiftSmooth.thF_shift_all | exact GlobalTheory.ThetaShiftSmooth.thF_shift_all | (intros; apply GlobalTheory.ThetaShiftSmooth.thF_shift_all <;> assumption)
end

