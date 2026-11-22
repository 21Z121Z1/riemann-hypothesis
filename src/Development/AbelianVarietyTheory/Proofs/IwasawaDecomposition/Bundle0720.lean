import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevJCosetsOfFurther
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeans
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Formulas

variable {X : Type} [AddCommGroup X]

theorem evalW_add_left (w w' : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (w + w') B = evalW w B + evalW w' B := by
  unfold evalW
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

theorem evalW_zero_left (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW (0 : (X × X) →₀ ℤ) B = 0 := by
  simp [evalW]

theorem evalW_zsmul_left (k : ℤ) (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (k • w) B = k * evalW w B := by
  unfold evalW
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp only [smul_eq_mul, Int.cast_mul]
  ring

theorem evalW_single_left (p : X × X) (k : ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (Finsupp.single p k) B = k * B p.1 p.2 := by
  unfold evalW
  exact Finsupp.sum_single_index (by simp)

theorem evalW_finset_sum_left {ι : Type} (s : Finset ι) (f : ι → (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (∑ i ∈ s, f i) B = ∑ i ∈ s, evalW (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalW_zero_left]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evalW_add_left, ih]

theorem evalW_lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (lamW D N n 𝓜 r w a) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y))) := by
  simp only [lamW, evalW_zsmul_left, evalW_add_left, evalW_finset_sum_left, evalW_single_left]
  push_cast
  simp

theorem kDen_mul_evalR_baseFun {O : Type} [CommRing O] [Module.Finite ℤ O] [Module O X] [Module.Finite O X]
    [Module.Finite ℤ X] (D : ℕ) (φ : InvFun ℤ) (N n : ℕ) (𝓜 : Finset ℕ) {r : (Fin n → ℤ) →ₗ[ℤ] X}
    (hr : Function.Surjective r) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (kDen N n 𝓜 : ℝ) * evalR (baseFun O D φ 𝓜) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, classMin M (fun x z => B (r x) (r z)) y) := by
  have hE : ∀ M, (fineMean M).eval X (fun x z => B x z) =
      (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    intro M
    rw [(fineMean M).eval_eq hr]
    simp [fineMean]
  have key : ∀ M ∈ 𝓜, (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (((M : ℝ) + 1) ^ n)⁻¹ =
      ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := by
    intro M hM
    rw [← Finset.mul_prod_erase 𝓜 (fun M : ℕ => ((M : ℝ) + 1) ^ n) hM]
    have : ((M : ℝ) + 1) ^ n ≠ 0 := by positivity
    field_simp
  have hs : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y =
      ∑ M ∈ 𝓜, (∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun M hM => by rw [← mul_assoc, key M hM]
  have h1 : evalR (baseFun O D φ 𝓜) B = D * (evalR φ B + ∑ M ∈ 𝓜, (fineMean M).eval X (fun x z => B x z)) :=
    eval_baseFun D φ 𝓜 _
  rw [h1]
  simp only [hE, kDen]
  push_cast
  calc _ = (D : ℝ) * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) + N * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y)) := by ring
    _ = _ := by
      rw [hs, Finset.mul_sum]
      simp only [mul_assoc]

theorem classMin_le_of_nonneg (M : ℕ) {n : ℕ} {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (hB : ∀ x, 0 ≤ B x x)
    {y : Fin n → ZMod (M + 1)} {x : Fin n → ℤ} (hx : redV M x = y) : classMin M B y ≤ B x x :=
  csInf_le ⟨0, by rintro _ ⟨b, -, rfl⟩; exact hB b⟩ ⟨x, hx, rfl⟩

end Formulas

theorem exists_contact_baseFun_lamW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone H.bar X, (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  intro E _ _ _ H D φs 𝓜 X _ _ _ _ N m n u w r a hD hφ hN hu hS hr ha
  classical
  choose F hF using fun (M : ℕ) (y : Fin n → ZMod (M + 1)) =>
    GlobalTheory.T.dickson_exists_finite_subfamily_below m (fun a' : {a' : Fin n → ℤ // redV M a' = y} => fun j => (u j (r a'.1) (r a'.1)).toNat)
  let vec : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → (Fin n → ℤ) → Fin m → ℤ :=
    fun M y a' i => u i (r (a M y)) (r (a M y)) - u i (r a') (r a')
  have hI := GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φs N m u w hφ hu hS
  have hsum : ∀ (t : Fin m → ℝ) (x z : X), (∑ i, t i • toReal (u i)) x z = ∑ i, t i * (u i x z : ℝ) := by
    intro t x z
    simp [LinearMap.sum_apply]
  have hP : 0 < ∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n := Finset.prod_pos fun _ _ => by positivity
  have hc : ∀ M ∈ 𝓜, 0 < (N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := fun M _ =>
    mul_pos (by exact_mod_cast hN) (Finset.prod_pos fun _ _ => by positivity)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD

  have hle_gen : ∀ B ∈ psdCone (id : ℤ → ℤ) X,
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B ≤ evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW]
    have h1 := ((hI.2 B hB).1)
    have h2 : ∀ M ∈ 𝓜, ∑ y, classMin M (fun x z => B (r x) (r z)) y ≤ ∑ y, B (r (a M y)) (r (a M y)) :=
      fun M _ => Finset.sum_le_sum fun y _ =>
        classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB (r x)) (ha M y)
    have h3 := Finset.sum_le_sum fun M hM => mul_le_mul_of_nonneg_left (h2 M hM) (hc M hM).le
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    exact mul_le_mul_of_nonneg_left (add_le_add h4 h3) hD'.le

  have hback : ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) →
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB hcl
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW, hI.1 B hB]
    congr 2
    exact Finset.sum_congr rfl fun M hM => by rw [Finset.sum_congr rfl fun y _ => hcl M hM y]
  refine ⟨⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
      (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _), ?_, ?_, ?_, ?_, hback⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet 𝓜) fun M _ =>
      Set.finite_iUnion fun y => (Finset.finite_toSet _).image _
  · intro β hβ hβ0
    have hB : toReal β ∈ psdCone H.bar X := by
      have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
        (fun i y => by fin_cases i; simpa using hβ0 y) (fun i => by fin_cases i; simp)
      simpa using this
    rw [← evalR_toReal]
    exact hle_gen _ (GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB)
  · intro B hB heq
    have hB' := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW] at heq
    have heq' := mul_left_cancel₀ hD'.ne' heq
    have h1 := (hI.2 B hB').1
    have hy : ∀ M, ∀ y, 0 ≤ B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y := fun M y =>
      sub_nonneg.2 (classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) (ha M y))
    have hT : 0 ≤ ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) :=
      Finset.sum_nonneg fun M hM => mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)
    have hT' : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) =
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y)) -
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
          ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_sub_distrib, mul_sub]
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    have hT0 : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) = 0 := by
      linarith
    have hW : (N : ℝ) * evalR φs B = evalW w B := by
      have : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φs B) = (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B := by
        linarith
      exact mul_left_cancel₀ hP.ne' this
    have hcl : ∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y)) := by
      intro M hM y
      have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun M hM =>
        mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)).1 hT0 M hM
      have e2 := (mul_eq_zero.1 e1).resolve_left (hc M hM).ne'
      have e3 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hy M y).1 e2 y (Finset.mem_univ _)
      linarith
    have hcm : ∀ M y (x : Fin n → ℤ), redV M x = y → classMin M (fun x z => B (r x) (r z)) y ≤ B (r x) (r x) :=
      fun M y x hx => classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) hx
    obtain ⟨t, ht0, rfl⟩ := (hI.2 B hB').2 hW
    refine ⟨t, ht0, ?_, rfl⟩
    intro v hv
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨M, hM, y, a', ha'F, rfl⟩ := hv
    have e := hcl M hM y
    have e' := hcm M y a'.1 a'.2
    rw [e, hsum, hsum] at e'
    rw [hsum] at e
    have : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    rw [this]
    linarith
  · intro t ht hA
    refine hback _ ⟨t, ht, rfl⟩ fun M hM y => ?_
    refine IsLeast.csInf_eq ⟨⟨a M y, ha M y, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a', ha'F, hle⟩ := hF M y ⟨x, hx⟩
    have hmem : vec M y a'.1 ∈ ⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
        (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _) := by
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨M, hM, y, a', ha'F, rfl⟩
    have h1 := hA _ hmem
    have h2 : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    have h3 : ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) ≤ ∑ i, t i * (u i (r x) (r x) : ℝ) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have p1 := hu.nonneg i (r a'.1)
      have p2 := hu.nonneg i (r x)
      have p3 : (u i (r a'.1) (r a'.1)).toNat ≤ (u i (r x) (r x)).toNat := hle i
      exact_mod_cast (show u i (r a'.1) (r a'.1) ≤ u i (r x) (r x) by omega)
    show (∑ i, t i • toReal (u i)) (r (a M y)) (r (a M y)) ≤ (∑ i, t i • toReal (u i)) (r x) (r x)
    rw [hsum, hsum]
    linarith

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellClass

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁]

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ γ) (e : X ≃ₗ[O] X₁) : IsCell bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pull r : LinearMap.BilinForm ℤ X₁ → LinearMap.BilinForm ℤ X) := by
  intro β β' h
  refine LinearMap.ext₂ fun a b => ?_
  obtain ⟨a, rfl⟩ := hr a
  obtain ⟨b, rfl⟩ := hr b
  exact LinearMap.congr_fun₂ h a b

theorem linearIndependent_pull_equiv {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : LinearIndependent ℤ γ)
    (e : X ≃ₗ[O] X₁) : LinearIndependent ℤ fun i => pull e.toLinearMap (γ i) :=
  h.map' (pullLin e.toLinearMap) (LinearMap.ker_eq_bot.2 (pull_injective e.surjective))

theorem isPrim_pull_equiv (e : X ≃ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁)
    (h : IsPrim bar (⟨β, hβ⟩ : balForms bar X₁)) :
    IsPrim bar (⟨pull e.toLinearMap β, pull_mem _ hβ⟩ : balForms bar X) := by
  intro k β' hk
  refine h k ⟨pull e.symm.toLinearMap β'.1, pull_mem _ β'.2⟩ (Subtype.ext (LinearMap.ext₂ fun a b => ?_))
  have := LinearMap.congr_fun₂ (congrArg Subtype.val hk) (e.symm a) (e.symm b)
  simpa using this

end Transport

theorem perModule {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hX : IsPolyFanOn H.bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell H.bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      ∃ e : X ≃ₗ[𝓞 E] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms H.bar X, IsPrim H.bar (⟨t, ht⟩ : balForms H.bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray H.bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone H.bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell H.bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone H.bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (GlobalTheory.T.cell_generator_mem_cone_of_smul_combination H.bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  intro E _ _ _ H q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField E q
  have key : ∀ k, letI := (hR k).1; ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell H.bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar (R k))) →
        ∃ e : (R k) ≃ₗ[𝓞 E] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule H φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily (𝓞 E) := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell H.bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim H.bar (⟨δ' i, hcell'.mem i⟩ : balForms H.bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.PolFan.CellClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridField

open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

def vPre (s : Stages) (v : HeightOneSpectrum (𝓞 s.toD7.host.F)) : HeightOneSpectrum (𝓞 s.B.toPre.host.F) := v

def toPl {P Q : Pre} (h : P = Q) (v : HeightOneSpectrum (𝓞 P.host.F)) : HeightOneSpectrum (𝓞 Q.host.F) := by
  subst h
  exact v

@[simp] theorem toPl_rfl {P : Pre} (v : HeightOneSpectrum (𝓞 P.host.F)) : toPl rfl v = v := rfl

theorem leastSplitAuxiliaryPrime_congr_preData {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : GlobalTheory.ChiGrid.q0 s.toD7 = GlobalTheory.ChiGrid.q0 s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq {s s' : Stages} {B₀ : Pre} (hs : s.B.toPre = B₀) (hs' : s'.B.toPre = B₀) {T T' : Type}
    {L : Formalism.IndefR.Links.LevCh s.toD7 T} {L' : Formalism.IndefR.Links.LevCh s'.toD7 T'} {sc : Consts} (G : GridData L sc)
    (G' : GridData L' sc) (hv : toPl hs' (vPre s' G'.pl.v0) = toPl hs (vPre s G.pl.v0)) {K : Type} [Field K]
    (e : K →+* ℂ) (hF : FieldHas G' e) : ∃ G'' : GridData L sc, G''.pl = G.pl ∧ FieldHas G'' e := by
  subst hs
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at hs'
  subst hs'
  have hv0 : G'.pl.v0 = G.pl.v0 := hv
  refine ⟨⟨G.pl, ⟨G'.ch.chiH, G'.ch.chi, G'.ch.chi_eq, G'.ch.triv, G'.ch.inf,
      fun i h1 h2 PP hPP => G'.ch.unr i h1 h2 PP ?_, G'.ch.lev1, G'.ch.wild,
      fun i h1 h2 PP hPP => G'.ch.lev0 i h1 h2 PP (hPP.trans hv0.symm)⟩, G.sp⟩, rfl, ?_⟩
  · intro h
    apply hPP
    rcases G'.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0))
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inr h)
  · refine ⟨hF.values, fun v hv => ?_⟩
    have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv0.symm) h2
      · exact absurd (h2.trans hv0) h1
      · rfl
    rw [hd]
    refine hF.roots v ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hv with h | h
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0.symm))
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inr h)

theorem exists_field_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
      (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩,
        GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  intro cDep b B₀
  classical

  let Wit : Set (HeightOneSpectrum (𝓞 B₀.host.F)) := {v | ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type)
    (L : Formalism.IndefR.Links.LevCh s.toD7 T) (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v}
  have hfin : Wit.Finite := by
    rcases Wit.eq_empty_or_nonempty with h | ⟨v₁, s₁, hs₁, T₁, L₁, G₁, -⟩
    · rw [h]
      exact Set.finite_empty
    · have hn : ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F) ≠ 0 := by
        subst hs₁
        exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec s₁.toD7).1.ne_zero
      refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F)).finite_toSet.subset ?_
      rintro _ ⟨s, hs, T, L, G, rfl⟩
      refine Formalism.L2.DIV.mem_primesOf.2 ⟨hn, ?_⟩
      subst hs
      rw [leastSplitAuxiliaryPrime_congr_preData hs₁]
      exact G.pl.basePlace_over_qZero
  have hex : ∀ v : Wit, ∃ Mv : IntermediateField ℚ ℂ, FiniteDimensional ℚ Mv ∧
      ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
        (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v ∧ FieldHas G Mv.val.toRingHom := by
    rintro ⟨v, s, hs, T, L, G, hv⟩
    obtain ⟨Mv, h1, h2⟩ := exists_fieldHas G
    exact ⟨Mv, h1, s, hs, T, L, G, hv, h2⟩
  choose Mv hMv hW using hex
  haveI := hfin.to_subtype
  haveI : ∀ v, FiniteDimensional ℚ (Mv v) := hMv
  refine ⟨⨆ v, Mv v, IntermediateField.finiteDimensional_iSup_of_finite, ?_⟩
  intro s hs _ T L G
  obtain ⟨s', hs', T', L', G', hv', hF⟩ := hW ⟨toPl hs (vPre s G.pl.v0), s, hs, T, L, G, rfl⟩
  have hF' : FieldHas G' (⨆ v, Mv v).val.toRingHom :=
    FieldHas.map (IntermediateField.inclusion (le_iSup Mv _)).toRingHom hF
  obtain ⟨G'', -, h⟩ := exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq hs hs' G G' hv' _ hF'
  exact ⟨G'', h⟩

end GlobalTheory.GridField

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_levJ_cosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi
  exact exists_levJ_cosets_of_further I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi
    (GlobalTheory.T.furtherPlaces_group_contains_chart_levels I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hFin hUl hchi)

end GlobalTheory.Mem.Col2.TwistLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rows_of_heq_data : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : Formalism.L2.TiedDataSK q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : GlobalTheory.Cp.SquareIntegrableColumnsCompatible T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ Formalism.L2.DIV.ColPins C.toS := by
  first | exact @GlobalTheory.Mem.R3.SelC.cols_of_witnesses | exact GlobalTheory.Mem.R3.SelC.cols_of_witnesses | (intros; apply GlobalTheory.Mem.R3.SelC.cols_of_witnesses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVarietyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  first | exact @GlobalTheory.SncChart.exists_coords | exact GlobalTheory.SncChart.exists_coords | (intros; apply GlobalTheory.SncChart.exists_coords <;> assumption)
end

