import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem basecond_exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), below P = v := by
  have hinj : Function.Injective (algebraMap (OF E) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))] at hx
      rw [hinj hx]
      exact v.asIdeal.zero_mem)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨⟨Q, hQ, hQne⟩, ?_⟩
  ext x
  simp [below, Ideal.under, ← hQv]

theorem basecond_natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  simp [below, Ideal.under, Ideal.mem_comap, map_natCast]

theorem isBaseCond_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  intro R H q0 w0 hspl hok
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hok.splits p hp).1

  have hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0 := by
    have h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
        exact (hprime _ (by simp)).ne_zero
    exact_mod_cast h
  have hle : cond0 H w0 ≤ (below w0).asIdeal := by
    unfold cond0
    first
    | exact Ideal.mul_le_right
    | exact Ideal.mul_le_left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h1 | h1
    · rw [← Ideal.zero_eq_bot] at h1
      have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h2
      exact hN0 h2
    · exact (below w0).ne_bot h1
  · intro h
    exact (below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro v hv

    obtain ⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by
      have hvp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      rcases hvp.dvd_or_dvd hv with h | h
      · have h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))
        push_cast at h1
        rcases v.isPrime.mem_or_mem h1 with h1 | h1
        · rcases v.isPrime.mem_or_mem h1 with h1 | h1
          · rcases v.isPrime.mem_or_mem h1 with h1 | h1
            · exact ⟨H.g 0, by simp, h1⟩
            · exact ⟨H.g 1, by simp, h1⟩
          · exact ⟨H.pde, by simp, h1⟩
        · exact ⟨H.pde', by simp, h1⟩
      · have h1 : (below w0).asIdeal = v.asIdeal :=
          ((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)
        refine ⟨q0, by simp, ?_⟩
        rw [← h1, basecond_natCast_mem_below]
        exact hok.referencePlaceOverPrime
    obtain ⟨P, hPv⟩ := basecond_exists_above v
    have hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
      rw [← basecond_natCast_mem_below, hPv]
      exact hpv
    obtain ⟨hpr, hp2, hdisc, hnorm⟩ := hok.splits p hp
    refine ⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩

    obtain ⟨e4, eb, e0⟩ := GlobalTheory.T.conductor_exponent_at_places R H q0 w0 hok P
    rw [← hPv]
    by_cases h4 : Over4 H P
    · rw [e4 h4]
    · by_cases hb : below P = below w0
      · rw [(eb hb).2]; norm_num
      · rw [e0 h4 hb]; norm_num

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplDescCompl
section
namespace GlobalTheory.RetractionComplement

open Formalism.MainNotions.N Matrix

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ}

theorem exists_retraction : ∃ l : k' →ₗ[k] k, ∀ c : k, l (algebraMap k k' c) = c := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
    (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
  exact ⟨g, fun c => by simpa using LinearMap.congr_fun hg c⟩

theorem form_mulVec (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k') :
    (fun i => l ((A.map (algebraMap k k')).mulVec x i)) = A.mulVec (fun i => l (x i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem ext_mulVec (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    (A.map (algebraMap k k')).mulVec (fun i => algebraMap k k' (v i))
      = fun i => algebraMap k k' (A.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def extSub (k' : Type) [Field k'] [Algebra k k'] (W : Submodule k (Fin n → k)) :
    Submodule k' (Fin n → k') :=
  Submodule.span k' ((fun (v : Fin n → k) (i : Fin n) => algebraMap k k' (v i)) '' W)

theorem form_mem (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (x : Fin n → k')
    (hx : x ∈ extSub k' W) : (fun i => l (x i)) ∈ W := by
  have key : ∀ c : k', (fun i => l (c * x i)) ∈ W := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro c
      convert W.smul_mem (l c) hw using 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | zero =>
      intro c
      convert W.zero_mem using 1
      funext i
      simp
    | add y z _ _ hy hz =>
      intro c
      convert W.add_mem (hy c) (hz c) using 1
      funext i
      simp [mul_add]
    | smul a y _ hy =>
      intro c
      convert hy (c * a) using 1
      funext i
      simp [mul_assoc]
  simpa using key 1

theorem extSub_stable (A : Matrix (Fin n) (Fin n) k) (W : Submodule k (Fin n → k))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (x : Fin n → k') (hx : x ∈ extSub k' W) :
    (A.map (algebraMap k k')).mulVec x ∈ extSub k' W := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [ext_mulVec]
    exact Submodule.subset_span ⟨_, hA w hw, rfl⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hy

def descCompl (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k')) :
    Submodule k (Fin n → k) where
  carrier := {v | ∃ x ∈ extSub k' W, ∃ u ∈ U, x + u = (fun i => algebraMap k k' (v i)) ∧
    (fun i => l (x i)) = 0}
  zero_mem' := ⟨0, Submodule.zero_mem _, 0, U.zero_mem, by funext i; simp, by funext i; simp⟩
  add_mem' := by
    rintro v w ⟨x, hx, u, hu, h1, h2⟩ ⟨x', hx', u', hu', h1', h2'⟩
    refine ⟨x + x', Submodule.add_mem _ hx hx', u + u', U.add_mem hu hu', ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      have b := congrFun h1' i
      simp only [Pi.add_apply, map_add] at a b ⊢
      rw [← a, ← b]; ring
    · funext i
      have a := congrFun h2 i
      have b := congrFun h2' i
      simp only [Pi.add_apply, map_add, Pi.zero_apply] at a b ⊢
      rw [a, b, add_zero]
  smul_mem' := by
    rintro c v ⟨x, hx, u, hu, h1, h2⟩
    refine ⟨algebraMap k k' c • x, Submodule.smul_mem _ _ hx, algebraMap k k' c • u,
      U.smul_mem _ hu, ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul] at a ⊢
      rw [← a]; ring
    · funext i
      have a := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a ⊢
      rw [← Algebra.smul_def, map_smul, a, smul_zero]

theorem isCompl_descCompl (l : k' →ₗ[k] k) (hl : ∀ c : k, l (algebraMap k k' c) = c)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (h : IsCompl (extSub k' W) U) : IsCompl W (descCompl l W U) := by
  have hmem : ∀ v ∈ W, (fun i => algebraMap k k' (v i)) ∈ extSub k' W :=
    fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  have hback : ∀ v : Fin n → k, (fun i => l (algebraMap k k' (v i))) = v :=
    fun v => funext fun i => hl (v i)
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨x, hx, u, hu, h1, h2⟩
    have hu' : u ∈ extSub k' W := by
      have e : u = (fun i => algebraMap k k' (v i)) - x := by rw [← h1]; abel
      rw [e]
      exact Submodule.sub_mem _ (hmem v hv) hx
    have hu0 : u = 0 := (Submodule.disjoint_def.mp h.disjoint) u hu' hu
    rw [hu0, add_zero] at h1
    rw [h1, hback] at h2
    exact h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (fun i => algebraMap k k' (v i)) ∈ extSub k' W ⊔ U := by
      rw [h.sup_eq_top]
      trivial
    obtain ⟨x, hx, u, hu, hxu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw⟩ : ∃ w : Fin n → k, w = fun i => l (x i) := ⟨_, rfl⟩
    have hwW : w ∈ W := hw ▸ form_mem l W x hx
    have hd : v - w ∈ descCompl l W U := by
      refine ⟨x - fun i => algebraMap k k' (w i), Submodule.sub_mem _ hx (hmem w hwW), u, hu, ?_, ?_⟩
      · funext i
        have e := congrFun hxu i
        simp only [Pi.add_apply, Pi.sub_apply, map_sub] at e ⊢
        rw [← e]
        ring
      · funext i
        simp [hw, hl]
    simpa using Submodule.add_mem_sup hwW hd

theorem descCompl_stable (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W)
    (hU : ∀ u ∈ U, (A.map (algebraMap k k')).mulVec u ∈ U) :
    ∀ v ∈ descCompl l W U, A.mulVec v ∈ descCompl l W U := by
  rintro v ⟨x, hx, u, hu, h1, h2⟩
  refine ⟨(A.map (algebraMap k k')).mulVec x, extSub_stable A W hA x hx,
    (A.map (algebraMap k k')).mulVec u, hU u hu, ?_, ?_⟩
  · rw [← Matrix.mulVec_add, h1, ext_mulVec]
  · rw [form_mulVec, h2, Matrix.mulVec_zero]

end SlopeTestRemainingChoices

theorem isSSRep_of_mapRep {Γ k k' : Type} [Group Γ] [Field k] [Field k'] {n : ℕ}
    (ι : k →+* k') (ρ : Γ →* GL (Fin n) k) (h : IsSSRep (mapRep ι ρ)) : IsSSRep ρ := by
  let _ : Algebra k k' := ι.toAlgebra
  have hcoe : ∀ g, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') =
      (ρ g : Matrix (Fin n) (Fin n) k).map (algebraMap k k') := fun _ => rfl
  obtain ⟨l, hl⟩ := exists_retraction (k := k) (k' := k')
  intro W hW
  have hWe : IsInv (mapRep ι ρ) (extSub k' W) := fun g x hx => by
    rw [hcoe]
    exact extSub_stable _ W (hW g) x hx
  obtain ⟨U, hU, hc⟩ := h _ hWe
  refine ⟨descCompl l W U, fun g => ?_, isCompl_descCompl l hl W U hc⟩
  exact descCompl_stable l _ W U (hW g) fun u hu => by
    rw [← hcoe]
    exact hU g u hu

end GlobalTheory.RetractionComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isCrys_of_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K P AI T d ρ U hU hinv
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  have hU' : IsUnit (U.map T.eB.symm) := by
    have := hU.map (T.eB.symm.mapMatrix (m := Fin d))
    simpa using this
  let Q : GL (Fin d) P.R.B := hU'.unit
  have hQ : (Q : Matrix (Fin d) (Fin d) P.R.B) = U.map T.eB.symm := hU'.unit_spec
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (qRep ρ g) = (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [qRep, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (qRep ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      apply (T.eB.mapMatrix (m := Fin d)).injective
      rw [map_mul, hmat g, hQ]
      have hA : T.eB.mapMatrix (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])).map (algebraMap ℚ_[l] P.R.B)) =
          (ρ g).val.map (Per.zB l) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        exact T.zB _
      have hB : T.eB.mapMatrix ((U.map T.eB.symm).map (((P.PD K).actB g).toRingEquiv.toRingHom)) =
          U.map (Per.σB (g : GQ l)) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        change T.eB ((P.PD K).actB g (T.eB.symm (U i j))) = _
        rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
      have hC : T.eB.mapMatrix (U.map T.eB.symm) = U := by
        ext i j
        simp
      rw [hA, hB, hC]
      exact hinv g)
    ((Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Dcris (P.PD K) (qRep ρ) := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (qRep ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : actVB (P.PD K) (qRep ρ) g y = TensorProduct.map (qRep ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [IsCrys, key, Module.finrank_fin_fun]

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrredOfAbsIrr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IrredOfAbsIrred

theorem isIrred_of_absIrrSub :
    ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ a ρ h
  classical
  obtain ⟨h0, -, h2⟩ := h
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  have hinj : Function.Injective f := f.injective
  refine ⟨fun hb => h0 ?_, fun U hU => ?_⟩
  · rw [hb, Submodule.span_eq_bot]
    rintro _ ⟨v, hv, rfl⟩
    have : v = 0 := by simpa using hv
    subst this
    ext x
    simp
  · have hst : IsInv (mapRep f ρ) (Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k)))) := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        refine Submodule.subset_span ⟨(ρ g : Matrix (Fin a) (Fin a) k).mulVec u, hU g u hu, ?_⟩
        ext p
        exact RingHom.map_mulVec f _ u p
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
    rcases h2 _ (Submodule.span_mono (Set.image_mono (fun _ _ => trivial))) hst with h1 | h1
    · left
      rw [Submodule.span_eq_bot] at h1
      rw [eq_bot_iff]
      intro v hv
      have := h1 _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_bot]
      ext p
      apply hinj
      simpa using congrFun this p
    · right
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
      let F : (Fin a → K) →ₗ[K] K :=
        { toFun := fun X => ∑ i, X i * f (φ (Pi.single i 1))
          map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun c X => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
            exact (Finset.mul_sum _ _ _).symm }
      have hF : ∀ X : Fin a → k, F (f ∘ X) = f (φ X) := by
        intro X
        conv_rhs => rw [← Finset.univ_sum_single X]
        simp only [map_sum]
        change ∑ i, f (X i) * f (φ (Pi.single i 1)) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        have : Pi.single i (X i) = X i • (Pi.single i (1 : k) : Fin a → k) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this, map_smul, smul_eq_mul, map_mul]
      have hker : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k))) ≤
          LinearMap.ker F := by
        rw [Submodule.span_le]
        rintro _ ⟨u, hu, rfl⟩
        have : φ u = 0 := hφ hu
        simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
      apply hφ0
      refine LinearMap.ext fun X => ?_
      have h3 : F (f ∘ X) = 0 := hker (by rw [h1]; exact Submodule.subset_span ⟨X, trivial, rfl⟩)
      rw [hF] at h3
      exact hinj (by rw [h3]; simp)

end GlobalTheory.IrredOfAbsIrred
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.Prism

theorem semiBC_basis (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (h : SemiBC u)
    (ι : Type) (e : Module.Basis ι A M) : ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  classical
  let g : (ι →₀ B) →ₗ[B] N := Finsupp.linearCombination B (fun i => u (e i))
  let v : M →ₛₗ[f] (ι →₀ B) :=
    { toFun := fun x => Finsupp.mapRange f f.map_zero (e.repr x)
      map_add' := fun x y => by
        ext i; simp
      map_smul' := fun a x => by
        ext i; simp }
  obtain ⟨w, hw, -⟩ := h (ι →₀ B) v
  have key : ∀ x : M, g (v x) = u x := by
    intro x
    conv_rhs => rw [← e.linearCombination_repr x]
    simp only [g, v, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    simp
  have h1 : w.comp g = LinearMap.id := by
    ext i
    simp [g, hw, v]
  have h2 : g.comp w = LinearMap.id := by
    obtain ⟨w0, -, huniq⟩ := h N u
    have a1 := huniq (g.comp w) (fun x => by simp [hw, key])
    have a2 := huniq LinearMap.id (fun x => rfl)
    rw [a1, a2]
  let E : N ≃ₗ[B] (ι →₀ B) := LinearEquiv.ofLinear w g h1 h2
  refine ⟨Module.Basis.ofRepr E, fun i => ?_⟩
  simp [Module.Basis.ofRepr, E, g]

end GlobalTheory.Prism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModulesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDuality_perfect_pair_finite_modules : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  first | exact @GlobalTheory.LocalPair.local_pair | exact GlobalTheory.LocalPair.local_pair | (intros; apply GlobalTheory.LocalPair.local_pair <;> assumption)
end

