import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem sum_mulVec_smul {ι E EE D O : Type} [CommRing O] [CommRing E] [CommRing EE] [Algebra O E]
    [Algebra O EE] [AddCommGroup D] [Module EE D] (jE : (ι → E) →ₐ[O] EE) {r : ℕ} (b : Fin r → D)
    (A : ι → Matrix (Fin r) (Fin r) E) (y : ι → Fin r → E) :
    ∑ m, jE (fun i => (A i).mulVec (y i) m) • b m =
      ∑ k, jE (fun i => y i k) • ∑ m, jE (fun i => A i m k) • b m := by
  have h : ∀ m, (fun i => (A i).mulVec (y i) m) =
      ∑ k, ((fun i => y i k) * (fun i => A i m k) : ι → E) := by
    intro m
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  simp only [h, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem isUnit_ι_E {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) : IsUnit (R.ι R.E) := by
  have hs : R.s ≠ 0 := by
    intro h
    have h1 := R.es
    have h2 := R.prime.two_le
    rw [h] at h1
    omega
  have h := R.EE_X.map R.φE
  rw [R.φE_ext, R.φ_X, map_mul, map_pow] at h
  exact (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_right h)

theorem coord_comm_φ_γ : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ S : Sys R n r, (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (S.G i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ S.M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (S.Φ i m k) : LetA O n) • (b m : W.DD T)) → (∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.φD x) = W.φD T (coord W R jE T (fun k => (b k : W.DD T)) x)) ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.γD x) = W.γD T W.gam (coord W R jE T (fun k => (b k : W.DD T)) x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    _ hE _ S hγ hφ
  obtain ⟨hext, -, -, hφE, hγE⟩ := hE
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [coord_apply, coord_apply, map_sum]
    refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
      (fun i => Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι)
      (fun i k => R.φE (x (i - 1) k))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.φD_smul, ← hφE]
    congr 1
    have h1 : ∀ m, jE (fun i => (Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι) m k) =
        jE (fun _ => Ring.inverse (R.ι R.E)) ^ S.M *
          algebraMap (LetA O n) W.EE (fun i => j (S.Φ i m k)) := by
      intro m
      rw [← hext, ← map_pow, ← map_mul]
      rfl
    have h2 : jE (fun _ => Ring.inverse (R.ι R.E)) *
        algebraMap (LetA O n) W.EE (fun _ => j R.E) = 1 := by
      rw [← hext (fun _ => R.E), ← map_mul, ← map_one jE]
      congr 1
      funext i
      exact Ring.inverse_mul_cancel _ (isUnit_ι_E R)
    simp only [h1, mul_smul, algebraMap_smul]
    rw [← Finset.smul_sum, ← hφ, ← algebraMap_smul W.EE ((fun _ => j R.E : LetA O n) ^ S.M),
      smul_smul, map_pow, ← mul_pow, h2, one_pow,
      one_smul]
  · rw [coord_apply, coord_apply, map_sum]
    refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
      (fun i => (S.G i).map R.ι) (fun i k => R.γE (x i k))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, ← hγE, hγ]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← algebraMap_smul W.EE (fun i => j (S.G i m k) : LetA O n), ← hext]
    rfl

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AlmostTrace

variable {l : ℕ} [Fact l.Prime]

theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono _ _ _
    fun (x : Om l) (hx : x ^ l ^ i = 1) => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _

theorem Ks_mono (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]

theorem Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx

theorem exists_mem_Ks (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h

theorem Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)

theorem exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl hinter hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  rw [hi₀] at hmem
  exact hmem

theorem sum_mem_Kinf (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex
  rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm

theorem exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)

theorem trace_almost_onto_of_levels
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]

end GlobalTheory.Cyc.AlmostTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedIntegralEqVolMulOrbitalIntegral
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.TruncInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem absK_ne_zero (A : Et F E) {t : A.K} (h : IsUnit t) : A.absK t ≠ 0 := by
  unfold Et.absK
  rw [dif_pos h]
  exact NNReal.coe_ne_zero.2 (IsUnit.map (distribHaarChar A.K) (Group.isUnit h.unit)).ne_zero

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := fun s => by
  have h := Set.indicator_const_preimage W s c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hW.isOpen, hW.isClosed.isOpen_compl, isOpen_empty]

end GlobalTheory.JR.TruncInt

open GlobalTheory.JR.TruncInt in

theorem GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  intro F E _ _ _ _ _ A hN hK ψ hψ m x y₀ hy₀ D hDo hDc φ hφ hsq
  classical
  obtain ⟨hNs, hNmul, hNt, hNu1, hNu2⟩ := hN
  obtain ⟨habs, habs1, hvol⟩ := hK
  set a : A.K := (x : A.K) * A.NL y₀ with ha_def
  have ha : IsUnit a := x.isUnit.mul (hNu2 y₀ hy₀)
  have hx : IsUnit (x : A.K) := x.isUnit
  have hkey : ∀ b : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * b → a * s ^ 2 = a + b := by
    intro b s hs
    rw [hs, mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul]
  have hsec : ∀ a' : A.K, ∀ s : A.K, s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) →
      A.NL (y₀ * algebraMap A.K A.L s) = a' := by
    intro a' s hs
    have h1 := hkey _ s hs
    rw [hNmul, hNs]
    apply hx.mul_left_cancel
    calc (x : A.K) * (A.NL y₀ * s ^ 2) = a * s ^ 2 := by rw [ha_def]; ring
      _ = _ := by rw [h1]; ring
  have habsT : ∀ a' : A.K, (x : A.K) * a' - a ∈ (D : Set A.K) →
      A.absK a' = A.absK a / A.absK x ∧ IsUnit a' := by
    intro a' hD
    obtain ⟨s, s', hs, hs', hss, hsq2, -⟩ := hsq _ hD
    have h1 := hkey _ s hsq2
    have h2 : (x : A.K) * a' = a * s ^ 2 := by rw [h1]; ring
    have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
    have hu : IsUnit a' := by
      have : IsUnit ((x : A.K) * a') := by rw [h2]; exact ha.mul (hsu.pow 2)
      exact isUnit_of_mul_isUnit_right this
    refine ⟨?_, hu⟩
    have h3 := congrArg A.absK h2
    rw [habs (x : A.K) a', habs a (s ^ 2), pow_two, habs s s, habs1 s s' hs hs' hss, mul_one, mul_one] at h3
    rw [eq_div_iff (absK_ne_zero A hx), ← h3]; ring
  set f : A.L → A.K := fun y => (x : A.K) * A.NL y - a with hf
  have hfc : Continuous f := (continuous_const.mul (EtMeas.continuous_NL A)).sub continuous_const
  have hSu : ∀ y, f y ∈ (D : Set A.K) → IsUnit y := fun y hy => hNu1 y (habsT _ hy).2
  set h : A.L → ℂ := fun y => φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) (f y) with hh
  show ∫ y, h y ∂(m.μL x) = _
  have hDcl : IsClosed (D : Set A.K) := AddSubgroup.isClosed_of_isOpen D hDo
  have hTest : IsTest h := by
    refine ⟨hφ.1.mul ((isLocallyConstant_indicator ⟨hDcl, hDo⟩ (1 : ℂ)).comp_continuous hfc), ?_⟩
    exact hφ.2.mul_right
  have hsupp : tsupport h ⊆ {y | IsUnit y} := by
    refine (closure_minimal ?_ (hDcl.preimage hfc)).trans ?_
    · intro y hy
      by_contra hn
      exact hy (by simp only [h, Set.indicator_of_notMem (show f y ∉ (D : Set A.K) from hn), mul_zero])
    · intro y hy
      exact hSu y hy
  have hμ := (GlobalTheory.JR.exists_meas_and_scale F E A ψ hψ).2 m x
  rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal (absK_nonneg A _)]
  have hxa : A.absK a / A.absK x ≠ 0 := div_ne_zero (absK_ne_zero A ha) (absK_ne_zero A hx)
  have hxaC : ((A.absK a / A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxa
  have hpt : ∀ y, h y = ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) := by
    intro y
    by_cases hy : f y ∈ (D : Set A.K)
    · rw [(habsT _ hy).1, mul_comm (h y), mul_inv_cancel_left₀ hxaC]
    · simp only [h, Set.indicator_of_notMem hy, mul_zero, zero_mul]
  have hI1 : ∫ y, h y ∂(m.μL 1) = ∫ y, ((A.absK a / A.absK x : ℝ) : ℂ) * (h y * ((A.absK (A.NL y) : ℂ))⁻¹) ∂(m.μL 1) :=
    integral_congr_ae (ae_of_all _ hpt)
  rw [hI1, integral_const_mul]
  let σ : A.K → A.L := fun a' =>
    if hb : (x : A.K) * a' - a ∈ (D : Set A.K) then y₀ * algebraMap A.K A.L (Classical.choose (hsq _ hb))
    else if he : ∃ y : A.L, A.NL y = a' then Classical.choose he else 0
  have hσD : ∀ a' (hb : (x : A.K) * a' - a ∈ (D : Set A.K)), ∃ s : A.K, σ a' = y₀ * algebraMap A.K A.L s ∧
      s ^ 2 = 1 + Ring.inverse a * ((x : A.K) * a' - a) ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
    intro a' hb
    obtain ⟨s', -, -, -, h4, h5⟩ := Classical.choose_spec (hsq _ hb)
    exact ⟨Classical.choose (hsq _ hb), by simp only [σ, dif_pos hb], h4, h5⟩
  have hσN : ∀ a', ((x : A.K) * a' - a ∈ (D : Set A.K) ∨ ∃ y : A.L, A.NL y = a') → A.NL (σ a') = a' := by
    intro a' hor
    by_cases hb : (x : A.K) * a' - a ∈ (D : Set A.K)
    · obtain ⟨s, hσs, hs2, -⟩ := hσD a' hb
      rw [hσs]; exact hsec a' s hs2
    · have he := hor.resolve_left hb
      simp only [σ, dif_neg hb, dif_pos he]
      exact Classical.choose_spec he
  have hσ : ∀ y : A.L, IsUnit y → A.NL (σ (A.NL y)) = A.NL y := fun y _ => hσN _ (Or.inr ⟨y, rfl⟩)
  rw [m.nat.2 σ hσ h hTest hsupp]
  set T : Set A.K := {a' | (x : A.K) * a' - a ∈ (D : Set A.K)} with hT
  have hTm : MeasurableSet T :=
    (hDo.preimage ((continuous_const.mul continuous_id).sub continuous_const)).measurableSet
  have hTN : T ⊆ {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'} := by
    intro a' hb
    refine ⟨σ a', ?_, hσN a' (Or.inl hb)⟩
    exact hNu1 _ (by rw [hσN a' (Or.inl hb)]; exact (habsT a' hb).2)
  have hNL0 : A.NL 0 = 0 := by simpa using hNs 0
  have hpt2 : ∀ a', A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ =
      T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' := by
    intro a'
    by_cases hb : a' ∈ T
    · obtain ⟨s, hσs, -, hφs⟩ := hσD a' hb
      have hNσ : A.NL (σ a') = a' := hσN a' (Or.inl hb)
      rw [Set.indicator_of_mem hb]
      congr 1
      unfold Et.orbL
      congr 1
      funext t
      have hft : f (t.1 * σ a') ∈ (D : Set A.K) := by
        show (x : A.K) * A.NL (t.1 * σ a') - a ∈ (D : Set A.K)
        rw [hNmul, hNt, hNσ, one_mul]; exact hb
      show φ (t.1 * σ a') * Set.indicator _ _ (f (t.1 * σ a')) = φ (t.1 * y₀)
      rw [Set.indicator_of_mem hft, mul_one, hσs, ← mul_assoc, hφs]
    · rw [Set.indicator_of_notMem hb]
      have hz : ∀ t : unitary A.L, h (t.1 * σ a') = 0 := by
        intro t
        have hft : f (t.1 * σ a') ∉ (D : Set A.K) := by
          by_cases he : ∃ y : A.L, A.NL y = a'
          · show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [hNmul, hNt, hσN a' (Or.inr he), one_mul]; exact hb
          · have h0 : σ a' = 0 := by simp only [σ, dif_neg (show ¬ ((x : A.K) * a' - a ∈ (D : Set A.K)) from hb), dif_neg he]
            show (x : A.K) * A.NL (t.1 * σ a') - a ∉ (D : Set A.K)
            rw [h0, mul_zero, hNL0, mul_zero, zero_sub]
            intro hD
            obtain ⟨s, s', -, -, hss, hs2, -⟩ := hsq _ hD
            have h1 := hkey _ s hs2
            rw [add_neg_cancel] at h1
            have hsu : IsUnit s := ⟨⟨s, s', hss, by rw [mul_comm]; exact hss⟩, rfl⟩
            have hu : IsUnit (a * s ^ 2) := ha.mul (hsu.pow 2)
            rw [h1, isUnit_zero_iff] at hu
            haveI := subsingleton_of_zero_eq_one hu
            exact he ⟨0, Subsingleton.elim _ _⟩
        simp only [h, Set.indicator_of_notMem hft, mul_zero]
      simp only [Et.orbL, hz, integral_zero, zero_mul]
  have hI2 : ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'}, A.orbL m.ν h (σ a') * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in {a' : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a'},
        T.indicator (fun a' => A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹) a' ∂m.μK :=
    integral_congr_ae (ae_of_all _ hpt2)
  rw [hI2, setIntegral_indicator hTm, Set.inter_eq_right.2 hTN]
  have hI3 : ∫ a' in T, A.orbL m.ν φ y₀ * ((A.absK a' : ℂ))⁻¹ ∂m.μK =
      ∫ a' in T, A.orbL m.ν φ y₀ * (((A.absK a / A.absK x : ℝ) : ℂ))⁻¹ ∂m.μK :=
    setIntegral_congr_fun hTm (fun a' hb => by simp only [(habsT a' hb).1])
  rw [hI3, setIntegral_const, Measure.real, hT, hvol m.μK m.sdK.1 x a _ hDo.measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 (absK_nonneg A _))]
  have hx0 : A.absK x ≠ 0 := absK_ne_zero A hx
  have ha0 : A.absK a ≠ 0 := absK_ne_zero A ha
  simp only [Complex.real_smul]
  have hx0C : ((A.absK x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have ha0C : ((A.absK a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  push_cast
  field_simp
end
end

