import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffException
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UniOff

open GlobalTheory.FinPlLoc (idem idem_mem_idAt idem_mem_intAt idem_mul_self cA_idem mem_idAt_iff ePl ePl_int evalV_ePl)

theorem intAt_neg {D : D7} {v : GlobalTheory.FinPl.Pl D} {z : AE D} (h : z ∈ intAt D (· = v)) : -z ∈ intAt D (· = v) :=
  ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem intAt_add {D : D7} {v : GlobalTheory.FinPl.Pl D} {z w : AE D} (h : z ∈ intAt D (· = v)) (h' : w ∈ intAt D (· = v)) :
    z + w ∈ intAt D (· = v) :=
  ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩

theorem idem_incA_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (o : 𝓞 D.host.E) :
    idem D (· = v) * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [map_mul, GlobalTheory.IdeleAA.finPart_incA]
  unfold idem
  rw [GlobalTheory.FinPlLoc.finPart_pair, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, o, rfl⟩

theorem idem_incA {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (e : D.host.E) :
    idem D P * incA D e = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] e := by
  unfold idem
  show (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_mem {D : D7} (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D)
    (P : GlobalTheory.FinPl.Pl D → Prop) (hP : ∀ w, ¬ P w → w ≠ v) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E}
    (hx : x ∈ L) : (fun m => idem D (· = v) * incA D (a * x m)) ∈ GlobalTheory.FinPl.latMul S 𝔞 L P := by
  apply AddSubgroup.subset_closure
  refine ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg (hP w hw)], a, ha, x, hx, ?_⟩
  funext m
  exact idem_incA _ _

theorem col_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (p : Fin c) {t : D.host.E} (ht : t ∈ 𝔟 p) : (fun m => t * d.a m p) ∈ d.lat Λ 𝔟 := by
  classical
  refine ⟨0, Λ.zero_mem, Pi.single p t, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; simpa using ht
    · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem uni_off : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D _ T L _ _ sc G W _ _ F hF ρ h M hM i j hij v hv o ho
  classical
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have h1' : 1 ≤ 2 * ρ + 1 := by omega
  have h2' : 2 * ρ + 1 ≤ D.R.m := by omega
  obtain ⟨hleB, heB, -, -⟩ := hF.hB ρ h

  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D W.ψ W.ψ_std
  obtain ⟨hA, hψ⟩ := hα v

  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) ⟨h2', Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have hMlat := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ (isSelfDualC_neg sdV) sdW (fun _ => True) M).1 hM.1

  set aB := (G.colDec (2 * ρ + 2) h1 h).a with haB
  set aJ := (G.colDec (2 * ρ + 1) h1' h2').a with haJ
  set p : Fin (2 * ρ + 2 - 1) := Fin.castLE (by omega) j with hp
  have hq : 2 * ρ - 1 - i.1 < 2 * ρ + 1 - 1 := by omega
  set q : Fin (2 * ρ + 1 - 1) := ⟨2 * ρ - 1 - i.1, hq⟩ with hqdef
  set colB : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun l => incA D (aB l p) with hcolB
  set g : AE D := ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l
    with hg

  have hcol : ∀ k, (M ⬝ (F.dB ρ h).jX) k j = incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) k := by
    intro k
    simp only [Matrix.mul_apply, GlobalTheory.MixModel.HypDec.jX, heB, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.MixModel.rat, Matrix.map_apply, colsOf, hcolB, map_mul, map_pow, hp]
    ring
  have hN : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = incA D (-D.host.xi0) * g := by
    have e1 : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = ((F.dJ ρ h).pX *ᵥ fun k => (M ⬝ (F.dB ρ h).jX) k j) i := rfl
    have e2 := GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing (G.colDec (2 * ρ + 1) h1' h2') (F.dJ ρ h) (by omega) (hF.hJ ρ h) i hq
      (fun k => (M ⬝ (F.dB ρ h).jX) k j)
    rw [← e1] at e2
    simp only [hcol] at e2
    have e3 : incA D ((-D.host.xi0) ^ (i.1 + 1)) * (incA D (-D.host.xi0) * g) =
        ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) *
          (incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) l) := by
      rw [hg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hp1 : (-D.host.xi0) ^ (j.1 + 1) = (-D.host.xi0) ^ (i.1 + 1) * (-D.host.xi0) := by rw [hij, pow_succ]
      rw [hp1, map_mul]
      ring
    have hunit : incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)), map_one]
    calc ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j
        = (incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1))) *
          ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j := by rw [hunit, one_mul]
      _ = incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * (incA D ((-D.host.xi0) ^ (i.1 + 1)) *
          (incA D (-D.host.xi0) * g)) := by rw [mul_assoc, e2, ← e3]
      _ = incA D (-D.host.xi0) * g := by rw [← mul_assoc, hunit, one_mul]

  set Φ : D.host.E → AE D := fun t => ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
    (idem D (· = v) * incA D t * g) with hΦ
  have hgen : ∀ t ∈ {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    rintro t ⟨a, ha, c', hc', c, hc, rfl⟩
    have hxB : (fun m => c * aB m p) ∈ G.Λ (.grid (2 * ρ + 2) 0) := by
      have e := G.sp.colLat (2 * ρ + 2) h1 h
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 2) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 2) h1 h) _ _ p hc
    have hxJ : (fun m => c' * aJ m q) ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
      have e := G.sp.colLat (2 * ρ + 1) h1' h2'
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 1) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 1) h1' h2') _ _ q hc'
    set y : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun m => idem D (· = v) * incA D (1 * (c * aB m p)) with hy
    have hyT : y ∈ latV (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) :=
      gen_mem _ {1} _ v _ (fun w hw => absurd trivial hw) rfl hxB
    set w : Fin (G.V (.grid (2 * ρ + 1) 0)).rank → AE D := fun m => idem D (· = v) * incA D (a * (c' * aJ m q)) with hw
    have hwv : w ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) :=
      gen_mem _ {a | a ∈ D.host.AA} _ v _ (fun w hw => hw) ha hxJ
    have hMy : M *ᵥ y ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := hMlat.2 y hyT
    have hMy' := GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace D _ _ _ v _ hMy
    have hyy : idem D (· = v) • (M *ᵥ y) = M *ᵥ y := by
      rw [← Matrix.mulVec_smul]
      congr 1
      funext m
      simp only [hy, Pi.smul_apply, smul_eq_mul, ← mul_assoc, idem_mul_self]
    rw [hyy] at hMy'
    have z1 := (hA _ _ _).1 hMy'
    have z2 := (hA _ _ _).1 hwv
    have hP := GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place D _ _ sdW v _ _ z1 z2
    have hw' : ∀ k, cA D ((((α⁻¹ : (AE D)ˣ) : AE D) • w) k) = cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) *
        incA D (D.host.conj (a * c')) * cA D (incA D (aJ k q)) := by
      intro k
      simp only [hw, Pi.smul_apply, smul_eq_mul, map_mul, cA_idem, GlobalTheory.IdeleAA.cA_incA]
      ring
    have hz' : ∀ l, (((α⁻¹ : (AE D)ˣ) : AE D) • (M *ᵥ y)) l = ((α⁻¹ : (AE D)ˣ) : AE D) * (idem D (· = v) * incA D c) *
        (M *ᵥ colB) l := by
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hy, hcolB]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [one_mul, map_mul]
      ring
    have hI := idem_mul_self (D := D) (· = v)
    convert hP using 1
    simp only [hw', hz', hΦ, hg, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * incA D (D.host.conj a) * incA D (D.host.conj c') *
      incA D c * (cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l))) * hI
  have hspan : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact hgen t ht
    | zero =>
      have : Φ 0 = 0 := by simp only [hΦ, map_zero, mul_zero, zero_mul]
      rw [this]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      have : Φ (x + y) = Φ x + Φ y := by simp only [hΦ, map_add]; ring
      rw [this]; exact intAt_add hx hy
    | smul o x _ hx =>
      have hI := idem_mul_self (D := D) (· = v)
      have : Φ (o • x) = (idem D (· = v) * incA D (o : D.host.E)) * Φ x := by
        rw [Algebra.smul_def]
        simp only [hΦ, map_mul]
        linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
          incA D (algebraMap (𝓞 D.host.E) D.host.E o) * incA D x * g)) * hI
      rw [this]; exact GlobalTheory.IdeleAA.intAt_mul (idem_incA_mem v o) hx
  obtain ⟨u, hu, hus⟩ := GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products G ρ p q (by simp [hp, hqdef]; omega) v hv
  have hz : idem D (· = v) * (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * g) ∈ intAt D (· = v) := by
    refine GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor D v u hu _ ?_
    have := hspan _ hus
    simp only [hΦ] at this
    convert this using 1; ring

  have hs : idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : incA D D.host.xi0⁻¹ * ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
      (idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) ∈ intAt D (· = v) := by
    have hx0 : incA D D.host.xi0⁻¹ * incA D (-D.host.xi0) = -1 := by
      rw [← map_mul, mul_neg, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_neg, map_one]
    rw [hN]
    convert intAt_neg hz using 1
    linear_combination (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) * g) * hx0
  have hoid : idem D (· = v) * o = o := (mem_idAt_iff _ o).1 ho.1
  have := (hψ _ hs).2 key o ho
  rw [← hoid]
  convert this using 2
  ring

end GlobalTheory.UniOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

section Map

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] (h : Sp T ⟶ Z.Hk)

def hkLift {x : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) : Gx x ⟶ Z.o₁.t.G.left :=
  Z.m₁.cart.1.lift (snd (Over.mk x) Xo.univ.t.G).left ((fst (Over.mk x) Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx])

def hkLift₂ {x' : Sp T ⟶ Xo.X} (hx' : x' = h ≫ Z.π₂) : Gx x' ⟶ Z.o₂.t.G.left :=
  Z.m₂.cart.1.lift (snd (Over.mk x') Xo.univ.t.G).left ((fst (Over.mk x') Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx'])

variable {h} {x x' : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)

@[reassoc] theorem hkLift_φ : hkLift Z h hx ≫ Z.m₁.cm.F = (snd (Over.mk x) Xo.univ.t.G).left :=
  Z.m₁.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift_hom : hkLift Z h hx ≫ Z.o₁.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ h :=
  Z.m₁.cart.1.lift_snd _ _ _

@[reassoc] theorem hkLift₂_φ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
  Z.m₂.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift₂_hom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
  Z.m₂.cart.1.lift_snd _ _ _

def hkMap : Gx x ⟶ Gx x' :=
  pullback.lift (f := (Over.mk x').hom) (g := Xo.univ.t.G.hom) (fst (Over.mk x) Xo.univ.t.G).left
    (hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F) (by
      simp only [Category.assoc]
      rw [Z.m₂.cart.1.w, Over.w_assoc Z.ψ, hkLift_hom_assoc, ← hx']; rfl)

@[reassoc] theorem hkMap_fst :
    hkMap Z hx hx' ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hkMap_snd :
    hkMap Z hx hx' ≫ (snd (Over.mk x') Xo.univ.t.G).left = hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F :=
  pullback.lift_snd _ _ _

@[reassoc] theorem hkMap_hkLift₂ : hkMap Z hx hx' ≫ hkLift₂ Z h hx' = hkLift Z h hx ≫ Z.ψ.left :=
  Z.m₂.cart.1.hom_ext (by rw [Category.assoc, hkLift₂_φ, hkMap_snd, Category.assoc])
    (by rw [Category.assoc, hkLift₂_hom, hkMap_fst_assoc, Category.assoc, Over.w Z.ψ, hkLift_hom])

end Map

section Square

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

theorem hkLift_isPullback (hx : x = h ≫ Z.π₁) :
    IsPullback (hkLift Z h hx) (fst (Over.mk x) Xo.univ.t.G).left Z.o₁.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₁.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₁) ?_ (hkLift_hom Z hx)
    Z.m₁.cart.1
  rw [hkLift_φ, ← hx]
  exact (IsPullback.of_hasPullback (Over.mk x).hom Xo.univ.t.G.hom).flip

theorem hkLift₂_isPullback (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift₂ Z h hx') (fst (Over.mk x') Xo.univ.t.G).left Z.o₂.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₂.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₂) ?_ (hkLift₂_hom Z hx')
    Z.m₂.cart.1
  rw [hkLift₂_φ, ← hx']
  exact (IsPullback.of_hasPullback (Over.mk x').hom Xo.univ.t.G.hom).flip

theorem hkMap_isPullback (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift Z h hx) (hkMap Z hx hx') Z.ψ.left (hkLift₂ Z h hx') := by
  refine IsPullback.of_bot ?_ (hkMap_hkLift₂ Z hx hx').symm (hkLift₂_isPullback Z hx')
  rw [hkMap_fst, Over.w Z.ψ]
  exact hkLift_isPullback Z hx

theorem hkMap_etale (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Etale (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Etale) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.1

theorem hkMap_surjective (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Surjective (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Surjective) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.2.1

end Square

section Fibre

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem isCan_hkLift {Ω : Type} [CommRing Ω] {χ : T →+* Ω} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x}
    (hx : x = h ≫ Z.π₁) (hp : IsCan χ pm) (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) :
    pm ≫ hkLift Z h hx = hkLift Z (spMap χ ≫ h) h₁ :=
  Z.m₁.cart.1.hom_ext (by rw [Category.assoc, hkLift_φ, hkLift_φ, hp.2.1])
    (by rw [Category.assoc, hkLift_hom, hkLift_hom, reassoc_of% hp.2.2])

theorem isFib_hkMap {Ω : Type} [CommRing Ω] (χ : T →+* Ω) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)
    {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} (hΨ : IsFib χ (hkMap Z hx hx') Ψ₁) :
    ∃ (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) (h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂), Ψ₁ = hkMap Z h₁ h₂ := by
  obtain ⟨pm, pm', hp, hp', e, f⟩ := hΨ
  have h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁ := by rw [hp.1, hx, Category.assoc]
  have h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂ := by rw [hp'.1, hx', Category.assoc]
  refine ⟨h₁, h₂, GlobalTheory.HeckeFrCompare.gx_ext (f.trans (hkMap_fst Z h₁ h₂).symm) ?_⟩
  rw [hkMap_snd Z h₁ h₂, ← isCan_hkLift_assoc Z hx hp h₁, ← hkMap_snd Z hx hx', ← reassoc_of% e, hp'.2.1]

end Fibre

end GlobalTheory.HeckeEx
end
end

