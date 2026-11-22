import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationBoundsInvariantCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem invariant_coord_bounds : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  intro l _ P K d ρ N hlow hhigh c hc hc0
  let b := Pi.basisFun ℚ_[l] (Fin d)
  let M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR := fun g =>
    (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l]))
  let e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => v i • β := by
    intro v β
    simp [e, b]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) (qRep ρ) g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, he_tmul, he_tmul]
      funext i
      simp only [M, qRep, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul,
        AlgEquiv.commutes, MonoidHom.coe_comp, Function.comp_apply]
      change algebraMap ℚ_[l] P.R.BdR ((((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) i) * _ = _
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PadicInt.algebraMap_apply]
      ring
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  set x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ c i with hx
  have hex : e x = c := by
    rw [hx, map_sum]
    funext j
    simp only [he_tmul, Finset.sum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
    simp
  have hxD : x ∈ DdR (P.PD K) (qRep ρ) := by
    rw [GlobalTheory.DRFil.mem_DdR]
    intro g
    apply e.injective
    rw [he, hex]
    exact hc g
  have hcoord : ∀ (a : ℤ) (y : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a → ∀ i, e y i ∈ (P.PD K).Fil a := by
    intro a y hy i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun y => e y i ∈ (P.PD K).Fil a) ?_ ?_ ?_ hy
    · simp
    · intro v β hβ
      rw [he_tmul]
      exact ((P.PD K).Fil a |>.restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro y z hy hz
      simpa only [map_add, Pi.add_apply] using Submodule.add_mem _ hy hz
  refine ⟨fun i => ?_, fun hall => hc0 ?_⟩
  · simpa [hex] using hcoord _ x (hlow hxD) i
  · have hxF : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hall i)
    have h0 : x ∈ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      ⟨hxD, hxF⟩
    rw [hhigh, Submodule.mem_bot] at h0
    rw [← hex, h0, map_zero]

end GlobalTheory.DRMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem deltaHom_unique_of_base : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  intro l _ A _ Q _ C _ DQ DC J JC i w tb hb hH h h' hδ hδ' hJ hi hw
  have hit : ∀ (g : Q →+* C), IsδMap DQ DC g → ∀ k x, g (DQ.δ^[k] x) = DC.δ^[k] (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]
  have hbα : ∀ α, h (tb.b α) = h' (tb.b α) := by
    intro α
    simp only [hb, Finsupp.prod, map_prod, map_pow, hit h hδ, hit h' hδ', hw]
  ext x
  have key : ∀ n, h x - h' x ∈ JC ^ n := by
    intro n
    have hF : ∀ α, α ∉ (tb.fin x n).toFinset → tb.c α x ∈ J ^ n := by
      intro α hα
      by_contra hc
      exact hα ((tb.fin x n).mem_toFinset.2 hc)
    have hap := tb.approx x n _ hF
    have hs : h (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) =
        h' (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← RingHom.comp_apply h i, hi, RingHom.comp_apply, hbα]
    have mem : ∀ g : Q →+* C, g.comp i = h.comp i →
        g (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) ∈ JC ^ n := by
      intro g hg
      have hm := Ideal.mem_map_of_mem g hap
      rw [Ideal.map_map, hg, Ideal.map_pow] at hm
      exact Ideal.pow_right_mono hJ n hm
    have e : h x - h' x = h (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) -
        h' (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      rw [map_sub, map_sub, hs]; ring
    rw [e]
    exact sub_mem (mem h rfl) (mem h' hi.symm)
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusComm
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add, ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceFormStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_restrictScalars_traceForm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  first | exact @GlobalTheory.DualLatDescent.dualLat_resQ | exact GlobalTheory.DualLatDescent.dualLat_resQ | (intros; apply GlobalTheory.DualLatDescent.dualLat_resQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

variable {l : ℕ} [Fact l.Prime]

variable (l) in

def ecoefQ (k₀ k i : ℕ) : ℚ_[l] := (l : ℚ_[l]) ^ k₀ * ((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹

variable (l) in

def ecoef (k₀ k i : ℕ) : ℤ_[l] :=
  ⟨if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0, by
    split_ifs with h
    · exact h
    · simp⟩

def kap (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) : Matrix (Fin d) (Fin d) (Per.Acris l) :=
  ∑ i ∈ Finset.range d, (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k i)) *
    (algebraMap (Ainf l) (Per.Acris l) (Per.zA l z) * C.t) ^ i) •
      (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ^ i

theorem ecoefQ_norm_le {d e m : ℕ} (k : ℕ) (hm : ¬ l ∣ m) (hd : d.factorial = l ^ e * m) {i : ℕ} (hi : i < d) :
    ‖ecoefQ l (e + k * d) k i‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hi.le
  obtain ⟨r, rfl⟩ : ∃ r, d = i + r := ⟨d - i, by omega⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hm0 : (m : ℚ_[l]) ≠ 0 := by
    rintro h
    exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  have h : (l : ℚ_[l]) ^ e * m = i.factorial * q := by
    exact_mod_cast (hd.symm.trans hq)
  have e1 : ecoefQ l (e + k * (i + r)) k i = (l : ℚ_[l]) ^ (k * r) * q * (m : ℚ_[l])⁻¹ := by
    unfold ecoefQ
    rw [show e + k * (i + r) = e + k * i + k * r by ring]
    field_simp
    rw [pow_add, pow_add]
    linear_combination ((l : ℚ_[l]) ^ (k * i) * (l : ℚ_[l]) ^ (k * r)) * h
  rw [e1, norm_mul, norm_mul, norm_inv, (Padic.norm_natCast_eq_one_iff (p := l)).2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hm), inv_one, mul_one]
  have h1 : ‖(l : ℚ_[l]) ^ (k * r)‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (q : ℤ)
  calc ‖(l : ℚ_[l]) ^ (k * r)‖ * ‖(q : ℚ_[l])‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ecoef_val {k₀ k i : ℕ} (h : ‖ecoefQ l k₀ k i‖ ≤ 1) :
    ((ecoef l k₀ k i : ℤ_[l]) : ℚ_[l]) = ecoefQ l k₀ k i := by
  show (if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0) = _
  rw [if_pos h]

theorem kap_zero (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) :
    kap C bk k₀ k Mn 0 = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold kap
  rw [Finset.sum_eq_single 0]
  · have h0 : ecoef l k₀ k 0 = (l : ℤ_[l]) ^ k₀ := by
      have hn : ‖ecoefQ l k₀ k 0‖ ≤ 1 := by
        simp only [ecoefQ, Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, inv_one]
        rw [norm_pow, Padic.norm_p]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
      apply Subtype.ext
      rw [ecoef_val hn]
      simp [ecoefQ]
    simp [h0]
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

end GlobalTheory.SstPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal

theorem constantCoeff_frobS_apply (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (p : (Wq l a)⟦X⟧) :
    constantCoeff (frobS l a p) = sigma l a (constantCoeff p) := by
  simp only [frobS]
  simp only [RingHom.coe_comp, Function.comp_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  simp

theorem eisPoly_distinguished_complete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  intro l _ a _ Ep ⟨hmon, hdeg, hdvd, w, hw⟩
  constructor
  · have hφ := (deltaS l a).φ_eq (Ep : (Wq l a)⟦X⟧)
    have h1 := congrArg constantCoeff hφ
    rw [show (deltaS l a).φ (Ep : (Wq l a)⟦X⟧) = frobS l a Ep from rfl, constantCoeff_frobS_apply] at h1
    simp only [Polynomial.constantCoeff_coe, map_add, map_pow, map_mul, map_natCast, hw] at h1
    set c := constantCoeff ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) with hc
    obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := (Fact.out : l.Prime).two_le; omega⟩
    have h2 : c = sigma l a (w : Wq l a) - (l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l := by
      have hl0 : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)
      apply mul_left_cancel₀ hl0
      have : ((l : Wq l a) * w) ^ l = (l : Wq l a) * ((l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l) := by
        have e : (l : Wq l a) ^ l = (l : Wq l a) ^ (k + 2) := by rw [← hk]
        rw [mul_pow, e]; ring
      rw [this] at h1
      linear_combination -h1
    rw [isUnit_iff_constantCoeff, ← hc, h2]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow k.succ_ne_zero, zero_mul, sub_zero]
    rw [WittVector.constantCoeff_apply, coeff_sigma, ← WittVector.constantCoeff_apply]
    exact pow_ne_zero _ ((w.isUnit.map (WittVector.constantCoeff (p := l) (R := Fq l a))).ne_zero)
  · set e := Ep.natDegree with he
    haveI : NeZero e := ⟨hdeg.ne'⟩
    have hP : Polynomial.C (l : Wq l a) ∣ Ep - Polynomial.X ^ e := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i e with h | rfl | h
      · rw [if_neg h.ne, sub_zero]; exact hdvd i h
      · have h1 : Ep.coeff e = 1 := hmon.coeff_natDegree
        rw [if_pos rfl, h1, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hP
    have hS : (Ep : (Wq l a)⟦X⟧) = X ^ e + (l : (Wq l a)⟦X⟧) * (q : (Wq l a)⟦X⟧) := by
      have := congrArg (fun p : Polynomial (Wq l a) => (p : (Wq l a)⟦X⟧)) hq
      simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
        map_natCast] at this
      have hc : ((l : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = l := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l a)) l
      rw [hc] at this
      linear_combination this
    have hJ : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)} =
        Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem, hS,
          show (X : (Wq l a)⟦X⟧) ^ e + (l : (Wq l a)⟦X⟧) * q = eis l a e + (l : (Wq l a)⟦X⟧) * (q - 1) by
            rw [eis]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem,
          show eis l a e = (Ep : (Wq l a)⟦X⟧) + (l : (Wq l a)⟦X⟧) * (1 - q) by rw [eis, hS]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [hJ]
    exact complete_eis l a e

end GlobalTheory.BKReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem eps0_unram_frob : ∀ (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.ntw.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v → (∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1) ∧ ∀ σ : Gen.GE D.nd, IsFrob (F := D.host.E) A (normV v) σ → ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  intro D i v hv A hA
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ D.host.E D.nd.Om (D.ntw.l i) σ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
      simp
    unfold eps0
    rw [MonoidHom.comp_apply, h1, map_one]
  · have h1 := cycZ_of_isFrob (l := D.ntw.l i) hv hA hσ
    show algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)
      ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : ℤ_[D.ntw.l i]) = _
    rw [h1, map_natCast]

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypePlace

theorem exists_place {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 :=
  _root_.GlobalTheory.IntegralNormSmallIdeal.exists_place_of_embedding c

theorem eq_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (a b : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (ha : ∀ x : 𝓞 E, x ∈ P ↔ ‖a (x : E)‖ < 1)
    (hb : ∀ x : 𝓞 E, x ∈ P ↔ ‖b (x : E)‖ < 1) (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) : a = b := by
  letI : Algebra E (PadicAlgCl l) := a.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := b.toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, a (σ y) = b y := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ha, hb]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    rw [e, hσ]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  ext x
  rw [← hσ, h2]
  rfl

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  intro h
  have h1 : H.galE H.conj = R.cc := H.galE_conjE
  rw [h, H.galE_one] at h1
  have h2 : (1 : ℤˣ) = -1 := congrArg (fun g : R.GG => g.1.2) h1
  exact absurd h2 (by decide)

theorem type_prime_places : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 = 1 ∧ ∀ w', IsConjPl D.host w w' → w' ≠ w) ∧ ∀ a b : D.host.E →+* Om (D.nd.l i), (∀ x : 𝓞 D.host.E, ‖a x‖ < 1 ↔ ‖b x‖ < 1) → a = b := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨fun w hw => ⟨(GlobalTheory.TypeDegOne.degree_one D i k hk).2 w hw, fun w' hc he => ?_⟩, fun a b hab => ?_⟩
  · subst he
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w' hw).2.2
    refine conj_ne_one D.host (inv_eq_one.1 (hP _ ?_))
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    exact (hc y (D.host.conj • y) rfl).symm
  · obtain ⟨v, hv, ha⟩ := exists_place a
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs v hv).2.2
    exact eq_of_stabilizer_trivial a b v.asIdeal ha (fun x => (ha x).trans (hab x)) hP

end GlobalTheory.TypePlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.ioE_closed | exact GlobalTheory.Decompl.ioE_closed | (intros; apply GlobalTheory.Decompl.ioE_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageSaturatedAdicClosedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRing_image_saturated_adicClosed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (x : RW LL) (e : W.EE), (l : RW LL) * x = E.tie.ioE e → ∃ e', x = E.tie.ioE e') ∧ ∀ x : RW LL, (∀ k : ℕ, ∃ e r, x - E.tie.ioE e = (l : RW LL) ^ k * r) → ∃ e, x = E.tie.ioE e := by
  first | exact @GlobalTheory.Decompl.Sat.ioE_saturated_closed | exact GlobalTheory.Decompl.Sat.ioE_saturated_closed | (intros; apply GlobalTheory.Decompl.Sat.ioE_saturated_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  first | exact @GlobalTheory.Per.frobenius_eq_mul_solvable | exact GlobalTheory.Per.frobenius_eq_mul_solvable | (intros; apply GlobalTheory.Per.frobenius_eq_mul_solvable <;> assumption)
end

