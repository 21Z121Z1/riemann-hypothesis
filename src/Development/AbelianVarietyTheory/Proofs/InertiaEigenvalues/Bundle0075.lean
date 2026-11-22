import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultant
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.DetAdResultant
theorem det_aeval_eq_resultant_of_splits {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (g : K[X]) (hg : g.Monic) (hs : g.Splits) :
    (aeval A g).det = resultant A.charpoly g := by
  rw [resultant_comm, resultant_eq_prod_eval g A.charpoly _ le_rfl hs, hg.leadingCoeff, one_pow, one_mul]
  let φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toMonoidHom
  have hφ : ∀ p, φ p = (aeval A p).det := fun p => rfl
  have h1 : ∀ x : K, φ (X - C x) = (-1) ^ Fintype.card ι * eval x A.charpoly := by
    intro x
    rw [hφ]
    simp only [map_sub, aeval_X, aeval_C, Matrix.eval_charpoly]
    rw [← Matrix.det_neg, neg_sub]
    rfl
  rw [← hφ]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hg]
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    Matrix.charpoly_natDegree_eq_dim, ← hs.natDegree_eq_card_roots]

theorem det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by
  let K := AlgebraicClosure E
  apply (algebraMap E K).injective
  have h := det_aeval_eq_resultant_of_splits (A.map (algebraMap E K)) (g.map (algebraMap E K))
    (hg.map _) (IsAlgClosed.splits _)
  rw [Matrix.charpoly_map, natDegree_map, natDegree_map, resultant_map_map] at h
  rw [← h, RingHom.map_det]
  congr 1
  have e : (algebraMap E K).mapMatrix (aeval A g) = (Algebra.ofId E K).mapMatrix (aeval A g) := rfl
  rw [e, ← aeval_algHom_apply, aeval_map_algebraMap]
  rfl
theorem det_det_charmatrix {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)

theorem toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply]
  have hr : ∀ M : Matrix ι₁ ι₂ E, (Matrix.stdBasis E ι₁ ι₂).repr M (a, j) = M a j := fun M => rfl
  have hψ : LinearMap.toMatrix b₂ b₁ (b₂.linearMap b₁ (b, k)) = Matrix.single b k 1 := by
    simp [Module.Basis.linearMap, Matrix.stdBasis_eq_single]
  rw [hr, LinearMap.sub_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply', map_sub,
    LinearMap.toMatrix_comp b₂ b₁ b₁, LinearMap.toMatrix_comp b₂ b₂ b₁, hψ]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Matrix.comp_apply, Matrix.map_apply, Matrix.charmatrix_apply, Matrix.transpose_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply, hjk, Matrix.diagonal_apply_ne _ hjk]
    by_cases hab : a = b
    · subst hab; simp [Ne.symm hjk]
    · simp [hab, Ne.symm hab, Ne.symm hjk]

theorem det_ad_eq_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁]
    [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂),
    LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      resultant f₁.charpoly f₂.charpoly := by
  intro E _ V₁ V₂ _ _ _ _ _ _ f₁ f₂
  let b₁ := Module.finBasis E V₁
  let b₂ := Module.finBasis E V₂
  rw [← LinearMap.det_toMatrix (b₂.linearMap b₁), toMatrix_ad b₁ b₂, Matrix.det_reindex_self,
    det_det_charmatrix, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end GlobalTheory.DetAdResultant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
section
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ModuleNorm

theorem distribHaarChar_transport {G H A B : Type} [Group G] [Group H]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [DistribMulAction H B] [ContinuousConstSMul H B]
    (e : A ≃ₜ+ B) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s) :=
    fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  have key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x) := fun x => by
    rw [inv_smul_eq_iff, ← he, smul_inv_smul]
  have hpre : e ⁻¹' (e.symm ⁻¹' K) = K := by
    ext x; simp
  have hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]
    simp
  have h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0 := by rw [hmap, hpre]; exact h0
  have hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤ := by rw [hmap, hpre]; exact hT
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]

theorem distribHaarChar_pi_two {G A : Type} [Group G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    (g : G) : distribHaarChar (Fin 2 → A) g = distribHaarChar A g ^ 2 := by
  borelize A
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hg : (Measure.addHaar : Measure A) (g • K) = distribHaarChar A g * Measure.addHaar K := by
    rw [distribHaarChar_eq_div h0 hT, ENNReal.div_mul_cancel h0 hT]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.pi fun _ : Fin 2 => (Measure.addHaar : Measure A)) (s := Set.univ.pi fun _ => K)
  · rw [Measure.pi_pi]; simp [h0]
  · rw [Measure.pi_pi]; simp [hT]
  · rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi]
    simp only [Pi.smul_apply, Fin.prod_univ_two, hg]
    push_cast
    ring

theorem distribHaarChar_eq_norm (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by
  let eC : (Fin 2 → K) ≃ₜ+ L :=
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }
  let kL : Lˣ := Units.map (algebraMap K L).toMonoidHom k
  have h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k :=
    distribHaarChar_transport eC k kL (fun x => by
      show e (k • x) = kL • e x
      simp only [Units.smul_def]
      rw [map_smul, Algebra.smul_def, smul_eq_mul]
      rfl)
  have h2 := distribHaarChar_pi_two (A := K) k
  let yS : Lˣ := Units.map (starRingEnd L).toMonoidHom y
  let sC : L ≃ₜ+ L :=
    { starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }
  have h3 : distribHaarChar L yS = distribHaarChar L y :=
    distribHaarChar_transport sC y yS (fun x => by
      show star (y • x) = yS • star x
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
      rfl)
  have h4 : kL = y * yS := Units.ext (by simp [kL, yS, h, starRingEnd_apply])
  have hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2 := by
    rw [← h2, ← h1, h4, map_mul, h3, sq]
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq

end GlobalTheory.JR.ModuleNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology Classical

variable {K : UQ} (B : InvAlg K) {ι : Type}

abbrev al (K : UQ) (a : K.O) : K.E := algebraMap K.O K.E a

def InDual (s : B.A) (M : Submodule K.O B.A) : Prop :=
  ∀ z ∈ M, Algebra.trace K.E B.A (s * z) ∈ (algebraMap K.O K.E).range

def indM (M : Submodule K.O B.A) (y : B.A) : ℚ := if y ∈ M then 1 else 0

def indD (M : Submodule K.O B.A) (s : B.A) : ℚ := if InDual B s M then 1 else 0

def dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) : ℚ :=
  ∑ J ∈ I.powerset, (-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)

def term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) : ℚ :=
  dlt π I (indM B M) u * dlt π I' (indD B M) s

def HH (π : ι → B.A) (I I' : Finset ι) (u s : B.A) : ℚ :=
  ∑ᶠ M ∈ B.Lin, B.sgnLat M * term B π I I' u s M

def eS (e : ι → B.A) (I : Finset ι) : B.A := ∑ i ∈ I, e i

def Pos (a : K.O) (e : ι → B.A) (N : ℕ) (M : Submodule K.O B.A) (p : ι → ℤ) : Prop :=
  ∀ i, (∀ r : B.A, IsIntegral K.O r → (al K a ^ (p i + N)) • (e i * r) ∈ M) ∧
    ∀ m ∈ M, IsIntegral K.O ((al K a ^ (-p i)) • (e i * m))

def chi (e : ι → B.A) (I : Finset ι) (y : B.A) : ℚ :=
  K.eta (Algebra.norm K.E (y * eS B e I + (1 - eS B e I)))

def IsPre [Fintype ι] (e : ι → B.A) (S : Finset ι) : Prop :=
  CompleteOrthogonalIdempotents e ∧ ∀ i, ∃ f : B.A, IsIdempotentElem f ∧ f ≠ 0 ∧
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
    (i ∈ S → e i = f ∧ B.σ f = f) ∧ (i ∉ S → f * B.σ f = 0 ∧ e i = f + B.σ f)

def IsFrame [Fintype ι] (e π : ι → B.A) (S : Finset ι) : Prop :=
  IsPre B e S ∧ ∀ i ∈ S, B.Plus (π i) ∧ π i * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E (π i)) = -1

def Win (I I' : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i, -(L : ℤ) ≤ p i ∧ p i ≤ 2 * k + L ∧ (i ∈ I → 2 * (k : ℤ) - L ≤ p i) ∧ (i ∈ I' → p i ≤ L)

def Mid (S : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i ∉ S, (L : ℤ) ≤ p i ∧ p i ≤ 2 * k - L

theorem eta_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add, zpow_add₀ (by norm_num)]

theorem eta_sq (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp

theorem abs_eta (x : K.E) : |K.eta x| = 1 := by
  unfold UQ.eta; simp

theorem abs_indM (M : Submodule K.O B.A) (y : B.A) : |indM B M y| ≤ 1 := by
  unfold indM; split_ifs <;> simp

theorem abs_indD (M : Submodule K.O B.A) (y : B.A) : |indD B M y| ≤ 1 := by
  unfold indD; split_ifs <;> simp

theorem abs_dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : A) :
    |dlt π I f y| ≤ 2 ^ I.card := by
  unfold dlt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ I.powerset, |(-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)| ≤ ∑ J ∈ I.powerset, (1 : ℚ) :=
        Finset.sum_le_sum fun J _ => by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hf _
    _ = 2 ^ I.card := by simp [Finset.card_powerset]

theorem abs_term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)

theorem dlt_eq_zero {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) (i : ι) (hi : i ∈ I)
    (h : ∀ J ⊆ I.erase i, f (π i * ((∏ j ∈ J, π j) * y)) = f ((∏ j ∈ J, π j) * y)) : dlt π I f y = 0 := by
  unfold dlt
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i I)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJ' : i ∉ J := fun h => Finset.notMem_erase i I (Finset.mem_powerset.1 hJ h)
  rw [Finset.prod_insert hJ', Finset.card_insert_of_notMem hJ', mul_assoc, h J (Finset.mem_powerset.1 hJ)]
  ring

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
section
noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]

def dcMapLe {Γ W K : Subgroup G} (hWK : W ≤ K) : DC Γ W → DC Γ K :=
  Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)

def dcOfCoset (Γ W K : Subgroup G) (t : G) : K ⧸ W.subgroupOf K → DC Γ W :=
  Quotient.lift (fun k : K => (Quotient.mk (dcSetoid Γ W) (t * k))) (by
    intro a b hab
    apply Quotient.sound
    have h := (QuotientGroup.leftRel_apply).1 hab
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨1, Γ.one_mem, (a : G)⁻¹ * b, by simpa using h, ?_⟩
    simp [mul_assoc])

theorem dcOfCoset_mk (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := rfl

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

theorem fiber_card_mul_stabCard {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K) (t : G)
    (ht : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) (k : K) :
    Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} *
      stabCard Γ W (t * k) = stabCard Γ K t := by
  classical
  set A := {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
  set B := {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)}
  set T := {δ : Γ // (t * k)⁻¹ * (δ : G) * (t * k) ∈ W}
  have hT : stabCard Γ W (t * k) = Nat.card T := rfl
  have hA : stabCard Γ K t = Nat.card A := rfl
  let φ : A → K := fun γ => ⟨t⁻¹ * (γ.1 : G) * t, γ.2⟩
  have hα : ∀ γ : A, dcOfCoset Γ W K t ((φ γ * k : K) : K ⧸ W.subgroupOf K) =
      dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
    intro γ
    rw [dcOfCoset_mk, dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨(γ.1 : G)⁻¹, Γ.inv_mem γ.1.2, 1, W.one_mem, ?_⟩
    simp [φ, mul_assoc]
  let α : A → B := fun γ => ⟨(φ γ * k : K), hα γ⟩
  have hsurj : Function.Surjective α := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [dcOfCoset_mk, dcOfCoset_mk] at hx
      obtain ⟨γ, hγ, w, hw, e⟩ := Quotient.exact hx

      have hmem : t⁻¹ * γ⁻¹ * t ∈ K := by
        have : t⁻¹ * γ⁻¹ * t = (k' : G) * w * (k : G)⁻¹ := by
          have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
            calc (k : G) = t⁻¹ * (t * k) := by group
              _ = _ := by rw [e]; group
          rw [e']; group
        rw [this]
        exact K.mul_mem (K.mul_mem k'.2 (hWK hw)) (K.inv_mem k.2)
      refine ⟨⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩, ?_⟩
      apply Subtype.ext
      show ((φ _ * k : K) : K ⧸ W.subgroupOf K) = (k' : K ⧸ W.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
        calc (k : G) = t⁻¹ * (t * k) := by group
          _ = _ := by rw [e]; group
      have : ((φ ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩ * k)⁻¹ * k' : K) = (w⁻¹ : G) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [e']; group
      rw [this]; exact W.inv_mem hw
  have hfib : ∀ γ₀ : A, Nonempty ({γ : A // α γ = α γ₀} ≃ T) := by
    intro γ₀
    have key : ∀ γ : A, α γ = α γ₀ ↔ (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) ∈ W := by
      intro γ
      rw [Subtype.ext_iff]
      show ((φ γ * k : K) : K ⧸ W.subgroupOf K) = ((φ γ₀ * k : K) : K ⧸ W.subgroupOf K) ↔ _
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((φ γ₀ * k)⁻¹ * (φ γ * k) : K) : G) = (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]; group
      rw [this]
    refine ⟨{ toFun := fun γ => ⟨⟨(γ₀.1 : G)⁻¹ * γ.1.1, Γ.mul_mem (Γ.inv_mem γ₀.1.2) γ.1.1.2⟩, (key γ.1).1 γ.2⟩
              invFun := fun δ => ⟨⟨⟨(γ₀.1 : G) * δ.1, Γ.mul_mem γ₀.1.2 δ.1.2⟩, ?_⟩, ?_⟩
              left_inv := fun γ => by ext; simp
              right_inv := fun δ => by ext; simp }⟩
    · have h1 : t⁻¹ * ((γ₀.1 : G) * δ.1) * t =
          (t⁻¹ * γ₀.1 * t) * ((k : G) * ((t * k)⁻¹ * δ.1 * (t * k)) * (k : G)⁻¹) := by group
      rw [h1]
      exact K.mul_mem γ₀.2 (K.mul_mem (K.mul_mem k.2 (hWK δ.2)) (K.inv_mem k.2))
    · rw [key]
      simpa using δ.2
  have e : A ≃ B × T :=
    (Equiv.sigmaFiberEquiv α).symm.trans
      ((Equiv.sigmaCongrRight (fun b => by
          have hb := hsurj b
          exact Classical.choice (by
            obtain ⟨γ₀, hγ₀⟩ := hb
            subst hγ₀
            exact hfib γ₀))).trans (Equiv.sigmaEquivProd B T))
  rw [hT, hA, Nat.card_congr e, Nat.card_prod]

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass
open scoped BigOperators

theorem dcOfCoset_surj {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (d : DC Γ W) (hd : dcMapLe hWK d = Quotient.mk (dcSetoid Γ K) t) :
    ∃ k : K, d = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
  induction d using Quotient.inductionOn with
  | h g =>
    have h2 : (dcSetoid Γ K) g t := Quotient.exact hd
    obtain ⟨γ, hγ, κ, hκ, e⟩ := (dcSetoid Γ K).iseqv.symm h2
    refine ⟨⟨κ, hκ⟩, ?_⟩
    rw [dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨γ⁻¹, Γ.inv_mem hγ, 1, W.one_mem, ?_⟩
    simp [e, mul_assoc]

theorem dcMapLe_dcOfCoset {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [dcOfCoset_mk]
    apply Quotient.sound
    exact ⟨1, Γ.one_mem, (k : G)⁻¹, K.inv_mem k.2, by simp⟩

theorem mass_eq_relIndex_mul {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K)
    (hW : Finite (DC Γ W)) (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    W.relIndex K ≠ 0 ∧ mass Γ W = (W.relIndex K : ℚ) * mass Γ K := by
  classical
  haveI := hW
  haveI : Finite (DC Γ K) := finite_dc_of_le hWK

  have hfibre : ∀ d : DC Γ W, Finite {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K 1 x = d} := by
    intro d
    by_cases hne : ∃ x : K ⧸ W.subgroupOf K, dcOfCoset Γ W K 1 x = d
    · obtain ⟨x, rfl⟩ := hne
      induction x using QuotientGroup.induction_on with
      | H k =>
        have h1 := fiber_card_mul_stabCard Γ W K hWK 1 (hfin 1) k
        have h2 := stabCard_pos (Γ := Γ) (K := K) 1 (hfin 1)
        have h3 : 0 < Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)} := by
          rcases Nat.eq_zero_or_pos (Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)}) with h | h
          · rw [h, zero_mul] at h1; omega
          · exact h
        exact (Nat.card_pos_iff.1 h3).2
    · push_neg at hne
      exact Finite.of_injective (β := Empty) (fun x => (hne x.1 x.2).elim) (fun x => (hne x.1 x.2).elim)
  haveI : Finite (K ⧸ W.subgroupOf K) :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv (dcOfCoset Γ W K 1))
  have hidx : W.relIndex K = Nat.card (K ⧸ W.subgroupOf K) := rfl
  have hne0 : W.relIndex K ≠ 0 := by
    rw [hidx]; exact Nat.card_ne_zero.2 ⟨⟨(1 : K)⟩, inferInstance⟩
  refine ⟨hne0, ?_⟩
  haveI := Fintype.ofFinite (DC Γ W)
  haveI := Fintype.ofFinite (DC Γ K)
  haveI := Fintype.ofFinite (K ⧸ W.subgroupOf K)

  have hfib : ∀ c : DC Γ K,
      ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c), ((stabCard Γ W d.out : ℕ) : ℚ)⁻¹ =
        (W.relIndex K : ℚ) * ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹ := by
    intro c
    set t := c.out with htdef
    have hct : c = Quotient.mk (dcSetoid Γ K) t := (Quotient.out_eq c).symm
    have hsK : (0 : ℚ) < stabCard Γ K t := by exact_mod_cast stabCard_pos t (hfin t)
    have hcard : (W.relIndex K : ℚ) = ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c),
        ((Finset.univ.filter (fun x => dcOfCoset Γ W K t x = d)).card : ℚ) := by
      rw [hidx, Nat.card_eq_fintype_card, ← Finset.card_univ]
      rw [Finset.card_eq_sum_card_fiberwise (f := dcOfCoset Γ W K t)
        (t := Finset.univ.filter (fun d => dcMapLe hWK d = c))]
      · push_cast; rfl
      · intro x _
        simp [dcMapLe_dcOfCoset, hct]
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := dcOfCoset_surj hWK t _ (hd.trans hct)
    have h1 := fiber_card_mul_stabCard Γ W K hWK t (hfin t) k
    rw [dcOfCoset_mk, stabCard_out]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← dcOfCoset_mk]
    have hsW : (0 : ℚ) < stabCard Γ W (t * k) := by
      have := stabCard_pos t (hfin t)
      rcases Nat.eq_zero_or_pos (stabCard Γ W (t * k)) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact_mod_cast h
    have h1' : (Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x =
        dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} : ℚ) * stabCard Γ W (t * k) = stabCard Γ K t := by
      exact_mod_cast h1
    field_simp
    linarith [h1']
  unfold mass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (dcMapLe hWK)]
  exact Finset.sum_congr rfl (fun c _ => hfib c)

end GlobalTheory.UnimodMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussPointStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussPoint' : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧ IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧ ∀ x, vV T'.V (i x) = vV T.V x := by
  first | exact @GlobalTheory.GaussPoint.exists_gaussPoint | exact GlobalTheory.GaussPoint.exists_gaussPoint | (intros; apply GlobalTheory.GaussPoint.exists_gaussPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  first | exact @GlobalTheory.PMonE.LangOnto.lang_onto | exact GlobalTheory.PMonE.LangOnto.lang_onto | (intros; apply GlobalTheory.PMonE.LangOnto.lang_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMaximalOrderHullSelfDualStableLatticeStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x, (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) → ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧ (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧ (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  first | exact @GlobalTheory.HullLat.exists_hull | exact GlobalTheory.HullLat.exists_hull | (intros; apply GlobalTheory.HullLat.exists_hull <;> assumption)
end

