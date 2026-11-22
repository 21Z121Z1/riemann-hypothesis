import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenBigCell
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellMat (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) : Matrix (Fin m) (Fin m) k :=
  fun c a => (b i).repr (g i (Fin.castLE hm a)) (Fin.castLE hm c)

theorem disjoint_step_iff_det_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (cellMat b g i m hm).det ≠ 0 := by
  have hinj : Function.Injective (Fin.castLE hm) := Fin.castLE_injective hm
  have hrepr (x : Fin m → k) (c : Fin (finrank k (V i))) :
      (b i).repr (∑ a, x a • g i (Fin.castLE hm a)) c =
        ∑ a, (b i).repr (g i (Fin.castLE hm a)) c * x a := by
    simp [map_sum, Finsupp.finset_sum_apply, mul_comm]
  constructor
  · intro hd h0
    obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : (∑ a, x a • g i (Fin.castLE hm a)) ∈ g.flags.step i m :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (step_flags_le.1 le_rfl _ (by simp))
    have h2 : (∑ a, x a • g i (Fin.castLE hm a)) ∈
        Submodule.span k (b i '' {a | m ≤ (a : ℕ)}) := by
      rw [Basis.mem_span_image]
      intro c hc
      by_contra hlt
      have hlt' : (c : ℕ) < m := not_le.1 hlt
      refine (Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hc)) ?_
      rw [hrepr]
      exact congrFun hMx ⟨c, hlt'⟩
    have h3 := Submodule.disjoint_def.1 hd _ h1 h2
    exact hx (funext (Fintype.linearIndependent_iff.1
      ((g i).linearIndependent.comp _ hinj) x h3))
  · intro hd
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h1' := mem_step_flags.1 h1
    have hv : v = ∑ a, (g i).repr v (Fin.castLE hm a) • g i (Fin.castLE hm a) := by
      conv_lhs => rw [← (g i).sum_repr v]
      symm
      refine Fintype.sum_of_injective _ hinj _ _ (fun a ha => ?_) fun a => rfl
      have : m ≤ (a : ℕ) := by
        by_contra hlt
        exact ha ⟨⟨a, not_le.1 hlt⟩, Fin.ext rfl⟩
      rw [h1' a this, zero_smul]
    have hMx : (cellMat b g i m hm).mulVec (fun a => (g i).repr v (Fin.castLE hm a)) = 0 := by
      funext c
      have h0 : (b i).repr v (Fin.castLE hm c) = 0 := by
        by_contra hne
        have := ((b i).mem_span_image.1 h2) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
        have hc := c.2
        simp only [Set.mem_setOf_eq, Fin.val_castLE] at this
        omega
      rw [hv, hrepr] at h0
      simpa [Matrix.mulVec, dotProduct, cellMat] using h0
    have hx := Matrix.eq_zero_of_mulVec_eq_zero hd hMx
    rw [hv]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun hx a, Pi.zero_apply, zero_smul]

theorem det_cellMat_mem_regFns (b : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    (fun g : Frames k V => (cellMat b g i m hm).det) ∈ regFns k V := by
  have h : (fun g : Frames k V => (cellMat b g i m hm).det) =
      ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k) •
        ∏ c, fun g : Frames k V => (b i).coord (Fin.castLE hm (σ c)) (g i (Fin.castLE hm c)) := by
    funext g
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply, cellMat]
  rw [h]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun c _ =>
    Algebra.subset_adjoin (.inl ⟨i, _, _, rfl⟩)) _

theorem isOpen_bigCell (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b : Frames k V) : IsOpen (bigCell b) := by
  refine isOpen_coinduced.2 ?_
  have h : Frames.flags ⁻¹' bigCell b = ⋂ i, ⋂ m : Fin (finrank k (V i) + 1),
      {g : Frames k V | (cellMat b g i m (Nat.lt_succ_iff.1 m.2)).det ≠ 0} := by
    ext g
    simp only [Set.mem_preimage, bigCell, Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun hg i m => (disjoint_step_iff_det_ne_zero b g i m _).1 (hg i m), fun hg i m => ?_⟩
    by_cases hm : m ≤ finrank k (V i)
    · exact (disjoint_step_iff_det_ne_zero b g i m hm).2 (hg i ⟨m, Nat.lt_succ_iff.2 hm⟩)
    · have he : {a : Fin (finrank k (V i)) | m ≤ (a : ℕ)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hm (le_trans ha a.2.le)
      rw [he, Set.image_empty, Submodule.span_empty]
      exact disjoint_bot_right
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun m =>
    isOpen_generateFrom_of_mem ⟨_, det_cellMat_mem_regFns b i m _, rfl⟩

example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpen (bigCell b) :=
  fun k _ ι _ V _ _ _ b => isOpen_bigCell k ι V b

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LuLowerLowerTriangular
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {n : ℕ}

def leadBlock (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  P.submatrix (Fin.castLE m.isLt) (Fin.castLE m.isLt)

def leadMinor (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : k := (leadBlock P m).det

def luNum (P : Matrix (Fin n) (Fin n) k) (a m : Fin n) : k :=
  ∑ l : Fin (m + 1), P a (Fin.castLE m.isLt l) * (leadBlock P m).cramer (Pi.single (Fin.last m) 1) l

def luLower (P : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := fun a m =>
  if a = m then 1 else if m < a then luNum P a m / leadMinor P m else 0

theorem luLower_apply_self (P : Matrix (Fin n) (Fin n) k) (a : Fin n) : luLower P a a = 1 := by
  simp [luLower]

theorem luLower_apply_of_lt (P : Matrix (Fin n) (Fin n) k) {a m : Fin n} (h : m < a) :
    luLower P a m = luNum P a m / leadMinor P m := by
  simp [luLower, h, h.ne']

theorem luLower_lowerTriangular (P : Matrix (Fin n) (Fin n) k) : (luLower P).BlockTriangular OrderDual.toDual :=
  fun a m h => by
    have h' : a < m := by simpa using h
    simp [luLower, h'.ne, not_lt.2 h'.le]

example (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : leadMinor P (Fin.last n) = P.det := by
  simp [leadMinor, leadBlock]

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
section
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.ZetaPole

theorem dedekindZeta_eq_tsum_ideal (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm.hasSum
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
  refine HasSum.tsum_eq (h.sigma fun n => ?_)
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (n : ℂ) ^ (-s) := by
    rintro ⟨I, rfl⟩; rfl
  simp only [this]
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have e : LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n =
      ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hs0]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
      simp
  rw [e]
  exact hasSum_fintype _

noncomputable def logFactor (n : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (n : ℝ) ^ (-s))

theorem rpow_lt_one {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)

theorem logFactor_nonneg {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : 0 ≤ logFactor n s := by
  have h1 := rpow_lt_one hn hs
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  unfold logFactor
  have := Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)
  linarith

theorem logFactor_le {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 1 ≤ s) : logFactor n s ≤ logFactor n 1 := by
  have h1 := rpow_lt_one hn one_pos
  have h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)
  unfold logFactor
  have := Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s))
    (by linarith) (by linarith)
  linarith

theorem ofReal_logFactor {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) :
    ((logFactor n s : ℝ) : ℂ) = -Complex.log (1 - (n : ℂ) ^ (-(s : ℂ))) := by
  have h1 := rpow_lt_one hn hs
  unfold logFactor
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

theorem summable_logFactor (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => logFactor (Ideal.absNorm v.asIdeal) s := by
  have hS := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).of_norm
  have pinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  have h := (Summable.clog_one_sub (hS.comp_injective pinj)).neg
  rw [← Complex.summable_ofReal]
  refine h.congr fun v => ?_
  rw [ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)]
  rfl

theorem norm_dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by
  classical
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by rintro h; rw [h] at hs'; norm_num at hs'
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs'
  have e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))
      = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hs0]
    · simp [hI]
  simp only [e1] at h
  simp only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _)
    (lt_trans one_pos hs)] at h
  rw [dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp,
    Complex.ofReal_re]

theorem not_injective_double_primes :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  intro K F _ _ _ _ S hS f hf hN
  set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc
  have key : ∀ s : ℝ, 1 < s →
      Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖ := by
    intro s hs
    rw [norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hK := summable_logFactor K hs
    have hF := summable_logFactor F hs
    have h1 := tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf
    have h2 := hF.comp_injective hf
    have e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) =
        fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s := by
      funext x
      simp only [Function.comp_apply, hN]
    rw [e] at h1 h2
    rw [h2.tsum_prod] at h1
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      tsum_mul_left, Nat.cast_ofNat] at h1
    have h3 := hK.sum_add_tsum_compl (s := hS.toFinset)
    rw [hS.coe_toFinset] at h3
    have h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c :=
      Finset.sum_le_sum fun v _ =>
        logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le
    have h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s =
      ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s := rfl
    linarith
  have tK := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have tF := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hle := le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)
    simp only [norm_mul]
    nlinarith)
  have hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖ :=
    norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  have : 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2 := by positivity
  linarith

end GlobalTheory.Mem.ZetaPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorResidueNonzeroOfSplit
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory

theorem rTensor_reduction_ne_zero_of_form_eq_one :
    ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  intro O R k _ _ _ _ _ _ ρ₀ hρ e f hf hε
  classical
  let b := Module.Free.chooseBasis ℤ O
  have key : ∀ (z : R ⊗[ℤ] O) i,
      TensorProduct.equivFinsuppOfBasisRight b (ρ₀.toIntAlgHom.toLinearMap.rTensor O z) i
        = ρ₀ (TensorProduct.equivFinsuppOfBasisRight b z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp
    | add x y hx hy => simp [hx, hy]
  have hmem : ∀ i, TensorProduct.equivFinsuppOfBasisRight b e i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    apply hρ
    rw [← key, hε]
    simp
  have he : e = (TensorProduct.equivFinsuppOfBasisRight b e).sum
      (fun i m => m • ((1 : R) ⊗ₜ[ℤ] b i)) := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply e]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    congr 1
    ext i m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hf, he, map_finsuppSum]
    refine Ideal.sum_mem _ fun i _ => ?_
    simp only [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (hmem i)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetIntegralMulLeft
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.AverageConst

@[to_additive setIntegral_add_left]
theorem setIntegral_mul_left {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (φ : Z → ℂ)
    (hφ : ∀ γ ∈ Λ, ∀ z, φ (γ * z) = φ z) (a : Z) : ∫ z in F, φ (a * z) ∂μ = ∫ z in F, φ z ∂μ := by
  have : SMulCommClass Z Λ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  rw [hF.setIntegral_eq (hF.smul_of_comm a) fun γ z => hφ γ γ.2 z]
  exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) φ F).symm

theorem average_const {Y Z A : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (Γ : AddSubgroup Y)
    [DiscreteTopology Γ] {K : Set Y} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) [AddCommGroup A] (χ : A → Y → ℂ)
    (h1 : ∀ a, Continuous (χ a)) (h2 : ∀ a x y, χ a (x + y) = χ a x * χ a y) (h3 : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (h4 : ∀ x, χ 0 x = 1) (h5 : ∀ a x, ‖χ a x‖ = 1) (h6 : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ)
    (ν : Measure Y) [ν.IsAddHaarMeasure] {G : Set Y} (hG : IsAddFundamentalDomain Γ G ν)
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (hfin : μ F ≠ ⊤)
    (k : Z → Y → ℂ) (kz : ∀ y, Continuous fun z => k z y) (ky : ∀ z, Continuous (k z)) {C : ℝ} (kb : ∀ z y, ‖k z y‖ ≤ C)
    (kΛ : ∀ γ ∈ Λ, ∀ z y, k (γ * z) y = k z y) (kΓ : ∀ γ ∈ Γ, ∀ z y, k z (γ + y) = k z y)
    (htw : ∀ a, (∀ y, χ a y = 1) ∨ ∃ (z₁ : Z) (c : ℂ), c ≠ 1 ∧
      ∀ z, ∫ y in G, χ a y * k (z₁ * z) y ∂ν = c * ∫ y in G, χ a y * k z y ∂ν) (y₀ : Y) :
    ∫ z in F, k z y₀ ∂μ = ∫ z in F, k z 0 ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (ν.restrict G) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν hG⟩
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y → ℂ, ∀ y, Φ y = ∫ z in F, k z y ∂μ := ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    rw [funext hΦ]
    exact continuous_of_dominated (bound := fun _ => C) (fun y => (kz y).aestronglyMeasurable)
      (fun y => .of_forall fun z => kb z y) (integrable_const _) (.of_forall ky)
  have hΦp : ∀ γ ∈ Γ, ∀ y, Φ (γ + y) = Φ y := fun γ hγ y => by simp only [hΦ, kΓ γ hγ]
  have hΦb : ∀ y, ‖Φ y‖ ≤ C * (μ.restrict F).real Set.univ := fun y => by
    rw [hΦ]; exact norm_integral_le_of_norm_le_const (.of_forall fun z => kb z y)
  have hint : ∀ a y₁, Integrable (fun y => χ a y * Φ (y₁ + y)) (ν.restrict G) := fun a y₁ =>
    Integrable.of_bound ((h1 a).mul (hΦc.comp (continuous_const.add continuous_id))).aestronglyMeasurable _
      (.of_forall fun y => by rw [norm_mul, h5, one_mul]; exact hΦb _)
  have hco : ∀ a, (∀ y, χ a y = 1) ∨ ∫ y in G, χ a y * Φ y ∂ν = 0 := fun a => (htw a).imp_right fun ⟨z₁, c, hc1, h⟩ => by
    have hm : StronglyMeasurable (Function.uncurry fun y z => χ a y * k z y) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => (h1 a).mul (ky z))
        fun y => (continuous_const.mul (kz y)).stronglyMeasurable
    have e : ∫ y in G, χ a y * Φ y ∂ν = ∫ z in F, ∫ y in G, χ a y * k z y ∂ν ∂μ := by
      simp only [hΦ, ← integral_const_mul]
      exact integral_integral_swap (Integrable.of_bound hm.aestronglyMeasurable C (.of_forall fun p => by
        rw [Function.uncurry, norm_mul, h5, one_mul]; exact kb _ _))
    have e2 := setIntegral_mul_left hc Λ μ hF (fun z => ∫ y in G, χ a y * k z y ∂ν)
      (fun γ hγ z => by simp only [kΛ γ hγ]) z₁
    simp only [h, integral_const_mul] at e2
    rw [e]
    exact (mul_left_eq_self₀.1 e2).resolve_left hc1
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero Y Γ K hK hcov A χ h1 h2 h3 h4 h5 h6 ν G
    inferInstance hG (fun y => Φ (y₀ + y) - Φ (0 + y))
    ((hΦc.comp (continuous_const.add continuous_id)).sub (hΦc.comp (continuous_const.add continuous_id)))
    (fun γ hγ y => by rw [add_left_comm, hΦp γ hγ, add_left_comm, hΦp γ hγ]) fun a => by
      have e := setIntegral_add_left add_comm Γ ν hG (fun y => χ a y * Φ y)
        (fun γ hγ y => by rw [h2, (h6 γ).2 hγ, one_mul, hΦp γ hγ]) y₀
      simp only [h2, mul_assoc, integral_const_mul] at e
      simp only [mul_sub]
      rw [integral_sub (hint a _) (hint a _), sub_eq_zero]
      simp only [zero_add]
      rcases hco a with h | h
      · rwa [h, one_mul] at e
      · rw [h] at e ⊢
        exact (mul_eq_zero.1 e).resolve_left fun h0 => by simpa [h0] using h5 a y₀
  have := congrFun key 0
  simp only [add_zero, Pi.zero_apply, sub_eq_zero] at this
  rw [← hΦ, ← hΦ, this]

end GlobalTheory.AverageConst
end

