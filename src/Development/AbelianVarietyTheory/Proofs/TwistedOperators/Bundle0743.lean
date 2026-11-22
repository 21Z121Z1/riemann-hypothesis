import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0724
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0737
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0736
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0620
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem intAf_mul' {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem pairA_mul' (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl

theorem mul_ePl {v : GlobalTheory.FinPl.Pl D} {α : Af D.host.F} (h : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * GlobalTheory.FinPlLoc.ePl D (· = v) = α := by
  classical
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (α * _) = evalV D.host.F w α
  rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · rw [if_pos hw, mul_one]
  · rw [if_neg hw, mul_zero, h w hw]

theorem smul_mem_homLat {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    {c : D.host.E} (hc : c ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹)
    {X : Matrix (Fin m) (Fin n) D.host.E} (hX : X ∈ 𝔪 • homLat Λ Λ') : c • X ∈ homLat Λ Λ' := by
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun x y hx hy => ?_)
  · have h1 : c * algebraMap (𝓞 D.host.E) D.host.E r ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hne]
      exact FractionalIdeal.mul_mem_mul hc (FractionalIdeal.mem_coeIdeal_of_mem _ hr)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have e : c • (r • Y) = o • Y := by
      rw [← algebraMap_smul D.host.E r Y, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact Submodule.smul_mem _ o hY
  · rw [smul_add]; exact add_mem hx hy

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {v : GlobalTheory.FinPl.Pl D}
    {z : AE D} (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) {x : Mx D m n}
    (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : z • x ∈ hatMx (homLat Λ Λ') := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, X, hX, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨α * β, intAf_mul' hα hβ, c • X, smul_mem_homLat h𝔪 hc hX, ?_⟩
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul']
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha

theorem val_le_one_of_mem_inv {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {a : D.host.E} (ha : a ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹) :
    Valued.v (algebraMap D.host.E (Kw Q) a) ≤ 1 := by
  obtain ⟨m, hm, hmQ⟩ := Set.not_subset.1 hQ
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h1 : a * algebraMap (𝓞 D.host.E) D.host.E m ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [← inv_mul_cancel₀ hne]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  rw [show Valued.v (algebraMap D.host.E (Kw Q) a) = Q.valuation D.host.E a from
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q a]
  have hm1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E m) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (Q.intValuation_le_one m)
      (not_lt.1 fun h => hmQ ((Q.intValuation_lt_one_iff_mem m).1 h))
  have ho1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤ 1 := Q.valuation_le_one o
  rw [ho, map_mul, hm1, mul_one] at ho1
  exact ho1

end GlobalTheory.DepthMap

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem val_cpt_le_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {v : GlobalTheory.FinPl.Pl D} {z : AE D}
    (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) :
    Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D z)) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    have e : pairA D.host.F 0 α ⊗ₜ[D.host.F] c =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c := by
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      show GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (incA D c)) = algebraMap D.host.E (Kw Q) c from Comparison₂.cpt_tmul Q c]
    have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
    exact mul_le_one' (((GlobalTheory.StdFrames.comp_toAd D).int _).1 hi Q) (val_le_one_of_mem_inv h𝔪 hQ hc)
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add, RingHom.map_add]; exact Valuation.map_add_le _ hx hy
  | neg x _ hx => rw [RingHom.map_neg, RingHom.map_neg, Valuation.map_neg]; exact hx

theorem cpt_idemSum_of_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P, Finset.sum_eq_single Q]
  · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
  · intro b hb hbQ; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q (Ne.symm hbQ)
  · intro h; exact absurd hQ h

theorem cpt_idemSum_of_not_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∉ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P]
  exact Finset.sum_eq_zero fun b hb => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q fun h => hQ (h ▸ hb)

theorem modul_not_le {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : Q ∉ P.W0) : ¬ P.modul sc ≤ Q.asIdeal := by
  classical
  intro h
  unfold Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le hle
  have h2 : P.w v = Q := HeightOneSpectrum.ext ((P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1)
  exact hQ (h2 ▸ Finset.mem_image_of_mem P.w hv)

end GlobalTheory.DepthMap
set_option maxHeartbeats 800000 in

open GlobalTheory.DepthMap in

theorem GlobalTheory.DepthMap.smul_mulVec_mem_latV : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  intro D hD T L μ0 hL sc G W M hM i hi u hu v hv y hy s hs
  classical
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  have P7 := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hm0 : G.pl.modul sc ≠ ⊥ := G.pl.modul_ne_bot sc
  have hmF : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hm0
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨-, -, -, -, -, P6, P7'⟩ := P7
  have key : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
        (G.Λ (.grid i 0) : Set _) (· = v) := by
    intro z hz
    obtain ⟨g, hg, g', hg', hid, hiff⟩ := P6 _ (inv_ne_zero hmF)
    have hzA : z ∈ idAt D (· = v) := ((hiff z).1 hz).1
    have hsplit : z • u = (e * z) • u + ((1 - e) * z) • u := by
      rw [← add_smul]; congr 1; ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
      have h2 := smul_mem_hatMx hm0 hz h1
      have h3 : (e * z) • u = z • (e • u) := by rw [mul_comm, mul_smul]
      rw [h3]
      have hhalf : IsHalf e (z • (e • u)) := fun a b => by
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_comm e z, mul_assoc, ← mul_assoc e e, GlobalTheory.PlaceDatum.idemSum_mul_self he]
      have h4 := GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hD hL G) hhalf h2
      refine (GlobalTheory.AscFinWit.mem_latO_at (fun a b => ?_)).1 h4
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hzA
    · have hint : finPart D ((1 - e) * z) ∈ intAE D := by
        refine ((GlobalTheory.StdFrames.comp_toAd D).int _).2 fun Q => ?_
        show Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D ((1 - e) * z))) ≤ 1
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
        by_cases hQ : Q ∈ G.pl.W0
        · rw [cpt_idemSum_of_mem he hQ, sub_self, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hc := cpt_idemSum_of_not_mem he hQ
          have hb := val_cpt_le_one hm0 (modul_not_le G.pl sc hQ) hz
          simp only [hc, sub_zero, one_mul]
          exact hb
      have hI : (1 - e) * z ∈ intAt D (· = v) := by
        refine ⟨?_, hint⟩
        exact Ideal.mul_mem_left _ _ hzA
      have hS := GlobalTheory.RowInt.smul_mem_latO_at D hD T L μ0 hL sc G W M hM
      exact hS i hi v _ hI u hu
  have hlatA : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • (u *ᵥ y) ∈ latA (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
    intro z hz
    rw [← Matrix.smul_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hsd (key z hz) hy
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, hsupp, a, ha, rfl⟩ := hs
    refine FractionalIdeal.mul_induction_on
      (C := fun a => (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) • (u *ᵥ y) ∈
        GlobalTheory.FinPl.latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v)) ha (fun b hb c hc => ?_)
      (fun x x' hx hx' => ?_)
    · have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] b) *
          (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul', mul_ePl hsupp]
      have hz : pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c ∈
          GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v :=
        AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPlLoc.ePl_int _, fun w hw => by
          rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw], c, hc, rfl⟩
      have hs' : pairA D.host.F 0 α ⊗ₜ[D.host.F] b ∈ GlobalTheory.SeeSaw.idV D.host.AA⁻¹ v :=
        AddSubgroup.subset_closure ⟨α, hα, hsupp, b, hb, rfl⟩
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c)) • (u *ᵥ y) ∈ _
      rw [e1, mul_smul]
      exact ((P7' _ _ _).1 (hlatA _ hz)).2 _ hs'
    · show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x + x')) • (u *ᵥ y) ∈ _
      rw [TensorProduct.tmul_add, add_smul]; exact add_mem hx hx'
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

theorem isTypeAt_lift_down : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.P i).V τ ((G.P i).S τ) (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint τ
  have hsig : (G.P i).V.SigOK := (hG.spaces.P i hi.le).sigOK
  have hgood := GlobalTheory.T.good_parameter_diagonal_nodes hP D hS G₀ Pl0 T A Ks R G hRB hG i hi τ
  have haut := GlobalTheory.T.negative_parabolic_theta_sixth hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint
  have hval := GlobalTheory.T.cusp_form_has_type_of_good_parameter hP R.θ (G.P i) τ hRB.inf hsig hgood
  refine GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P i).V τ ((G.P i).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hRB.inf hsig hgood haut ?_
  refine hasTypeAt_of_approx R.θ (G.P i).V τ ((G.P i).S τ) _ fun C hC δ hδ => ?_
  obtain ⟨χ, hχ, hC'⟩ := GlobalTheory.T.theta_lift_diagonal_level_preserved hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  refine ⟨χ, ?_, hC'⟩
  have hle : Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w} ≤
      GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ (G.P i).V τ ((G.P i).S τ) := by
    rw [Submodule.span_le]
    rintro f ⟨F, hF, w, rfl⟩
    exact hval F hF w
  exact hle hχ

end GlobalTheory.LiftTypeDn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThird
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.UpCuspLift

theorem up_isCuspFun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsCuspFun (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hLC hPr D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have haut := GlobalTheory.UpConjLift.up_isAutFunSm hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint
  have hCA := hLC D hS G₀ Pl0 T A Ks R G hR hG
  refine GlobalTheory.CuspApproxCompact.isCuspFun_of_approx D _ _ haut.cont haut.left fun C hC δ hδ => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    GlobalTheory.T.theta_lift_diagonal_approx_by_fock_lifts hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC δ hδ
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hval := fun l => GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) (G.ItU i (p l) (v l))
  have hc : Continuous (∑ l, F' l (G.ItU i (p l) (v l))) := by
    rw [Finset.sum_fn]
    exact continuous_finset_sum _ fun l _ => (hval l).1.cont
  have hl : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, (∑ l, F' l (G.ItU i (p l) (v l))) (γ * g) = (∑ l, F' l (G.ItU i (p l) (v l))) g := by
    intro γ hγ g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hval l).1.left γ hγ g
  have hmem := fun l => (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ (hval l).1.cont (hval l).1.left).1 (hval l).2
  refine ⟨∑ l, F' l (G.ItU i (p l) (v l)), hc, hl, ?_, ?_⟩
  · exact (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ hc hl).2 (Submodule.sum_mem _ fun l _ => hmem l)
  · intro h hh
    have e : (∑ l, F' l (G.ItU i (p l) (v l))) h =
        ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun l _ => ((hE l (p l) (v l) h).2).symm
    rw [e]
    exact happ h hh

end GlobalTheory.UpCuspLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShift0Model
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.LastVertexMove GlobalTheory.LastVertexInv GlobalTheory.FirstRowVertex

namespace GlobalTheory.FirstRowShift

private theorem locPl_under_mem_S0_or_Q {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    left
    rw [G.pl.w_over v hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

private theorem isSBHalf_of_half_mem_iff {D : D7} {A B : HSp D} {e : AE D} {Λ Λ' : AddSubgroup (WO A B)}
    (hΛ : ∀ x, IsHalf e x → (x ∈ Λ ↔ x ∈ Λ')) {Φ : WO A B → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ' Φ := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  refine ⟨h1, k, hk, fun u hu hue t => h2 u ((hΛ u hue).mpr hu) hue t, fun t ht => ?_⟩
  exact (hΛ _ (GlobalTheory.StdHalfLat.half_nsmul (h1 t ht) k)).mp (h3 t ht)

theorem sb_std_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {e : AE D}, t ∈ U → IsIdemSum e (locPl G t) → ∀ i : Fin D.R.m,
    ∀ Φ : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ,
      IsSBHalf e (latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T) : Set _) (G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) Φ →
      IsSBHalf e (stdLat S (.chi i D.R.m)) Φ := by
  intro D T L sc G W U S t e ht he i Φ hΦ
  have hS : DefNode D.R.m (Node.grid ((i : ℕ) + 1) D.R.m) := ⟨i.isLt, rfl⟩
  have hT : DefNode D.R.m (Node.grid (i : ℕ) D.R.m) := ⟨i.isLt.le, rfl⟩
  obtain ⟨a, ha, hga⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hS
  obtain ⟨b, hb, hgb⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hT
  have ha' : e * (a + cA D a) = 0 := ha
  have hb' : e * (b + cA D b) = 0 := hb
  obtain ⟨hS1, hS2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hS
  obtain ⟨hT1, hT2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hT
  have hga' : SuppAt a (G.pS (Pair.chi (i : ℕ) D.R.m)) (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) := by
    unfold SuppAt
    rw [mt_negGA]
    exact hga
  unfold GlobalTheory.LastVertexMove.stdLat
  refine isSBHalf_of_half_mem_iff (fun x hx => ?_) hΦ
  refine (GlobalTheory.StdHalfLat.mem_latO_iff_of_half (S := G.pS (Pair.chi (i : ℕ) D.R.m)) (T := G.pT (Pair.chi (i : ℕ) D.R.m))
    (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) (S.N.u (Node.grid (i : ℕ) D.R.m)).1
    (fun v hv => ?_) (fun v hv => ?_) hT1 hT2 ha' hb' hga' hgb hx).symm
  · rw [mt_negGA]
    exact hS1 v hv
  · rw [← map_inv (negGA (G.V (Node.grid ((i : ℕ) + 1) D.R.m))), mt_negGA]
    exact hS2 v hv

theorem actO_inv_actO {D : D7} {A B : HSp D} (g : GA D A) (h : GA D B) (u : WO A B) :
    actO A B g⁻¹ h⁻¹ (actO A B g h u) = u := by
  rw [← GlobalTheory.SplitLinear.actO_mul, inv_mul_cancel, inv_mul_cancel]
  simp [actO]

theorem vac_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)),
    (∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)), actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T)) →
    ∃ c : ℂ, W.om (.chi (firstIx D) D.R.m : Pair T) (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (firstIx D) D.R.m : Pair T)) = c • S.Z.vac (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S k hlat
  refine GlobalTheory.RowChiVac.vac_chi_scalar S (i := ((firstIx D : Fin D.R.m) : ℕ)) (firstIx D).isLt _ 1 ?_
  intro u
  have h := hlat (actO _ _
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2 u)
  rw [actO_inv_actO] at h
  exact h

end GlobalTheory.FirstRowShift

open GlobalTheory.FirstRowShift in

theorem GlobalTheory.FirstRowShift.rowShift0_model : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T} {e : AE D},
    t ∈ U → IsIdemSum e (locPl G t) →
    ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∃ c : ℂ, W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) =
        c • S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ∧
      ∀ Tm : (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ),
        IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
          (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (S.N.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (S.N.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) 1 (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) Tm →
        ∀ Φ : WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ,
          IsSBHalf e (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (G.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) Φ →
          GlobalTheory.FirstRowVertex.rowShift0 S k (Tm Φ) =
            c • Tm (fun y => Φ (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) := by
  intro D T L sc G W U S μ₀ hL t e ht he k hk
  have hlat := GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff S hL ht k hk
  obtain ⟨c, hc⟩ := vac_first S k hlat
  refine ⟨c, hc, fun Tm hT Φ hΦ => ?_⟩
  exact GlobalTheory.LastVertexTensor.om_model S (GlobalTheory.LastVertexInv.defPair_chi (T := T) (firstIx D))
    (GlobalTheory.LastVertexInv.inRange_chi (T := T) (firstIx D)) he Tm hT _ c hlat hc Φ (sb_std_row S ht he (firstIx D) Φ hΦ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingGramModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_doubling_gram_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  first | exact @GlobalTheory.LineSumV'.derSum | exact GlobalTheory.LineSumV'.derSum | (intros; apply GlobalTheory.LineSumV'.derSum <;> assumption)
end

