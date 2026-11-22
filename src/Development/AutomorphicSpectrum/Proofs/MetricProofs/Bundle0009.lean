import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0008

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_toWtS_homogeneous_coeff_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix Topology
open scoped ComplexOrder

theorem posDef_eventually_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (A : X → Matrix n n ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := isCompact_sphere 0 1
  have hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    simp only [dotProduct, mulVec]
    refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetSum _ fun j _ =>
        ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y),
      0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp [hKdef] at hy
    have h := h0.dotProduct_mulVec_pos hy0
    rw [Complex.lt_def] at h
    exact (hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K := by
    simp [hKdef, norm_smul, hn.ne']
  have h1 := hx _ hyK
  have e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y)) := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := (hH x).apply i j
    rw [Complex.star_def] at h
    rw [h]; ring
  rw [Complex.lt_def]
  refine ⟨?_, by simpa using him.symm⟩
  have := pos_of_mul_pos_right h1 (by positivity)
  simpa using this

theorem gramOf_isHermitian {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply, h, Ne.symm h]

theorem continuous_gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) :
    Continuous fun g : Matrix (Fin N) (Fin N) ℂ => gramHead hd k g := by
  unfold gramHead gramOf
  exact (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id).matrix_submatrix _ _

theorem isOpen_inFlagDomain (N j : ℕ) :
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} := by
  have h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef} := by
    refine isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_
    refine posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_)
      (fun g => ?_) g0 hg0
    · exact ((continuous_gramHead _ _).neg).matrix_elem a b
    · exact ((gramOf_isHermitian _ g).submatrix _).neg
  exact h1.inter h2

theorem gramOf_mul_of_preserves {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ)
    (hu : gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ))) :
    gramOf hd (u * g) = gramOf hd g := by
  unfold gramOf at hu ⊢
  rw [conjTranspose_mul]
  calc gᴴ * uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * (u * g)
      = gᴴ * (uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * u) * g := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem gramHead_of_triangular {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (b : Matrix (Fin N) (Fin N) ℂ)
    (hb : b.BlockTriangular id) :
    gramHead hd k b = (b.submatrix Subtype.val Subtype.val)ᴴ *
      diagonal (fun a : {a : Fin N // (a : ℕ) < k} => ((hd a : ℝ) : ℂ)) *
      b.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [gramHead, gramOf, submatrix_apply]
  rw [mul_apply, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, submatrix_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp)
    (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]
  rw [Finset.sum_filter_of_ne]
  intro l _ hl
  by_contra hlk
  apply hl
  have : b l i.1 = 0 := hb (by
    show i.1 < l
    have := i.2
    exact Fin.lt_def.2 (by omega))
  simp [this]

theorem sigForm_apply_ne_zero (N j : ℕ) (a : Fin N) : sigForm N j a ≠ 0 := by
  unfold sigForm; split_ifs <;> norm_num

theorem gramHead_det_ne_zero_of_triangular {N : ℕ} (hd : Fin N → ℝ) (hd0 : ∀ a, hd a ≠ 0) (k : ℕ)
    (b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
    (gramHead hd k b).det ≠ 0 := by
  have hbd : ∀ i, b i i ≠ 0 := by
    have h := (isUnit_iff_ne_zero.1 hu)
    rw [det_of_upperTriangular hb] at h
    exact fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0 := by
    have ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id :=
      fun i j hij => hb hij
    rw [det_of_upperTriangular ht]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1
  rw [gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]
  refine mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs
  exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)

theorem gramHead_det_ne_zero (N j : ℕ) (hj : j ≤ N) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : InFlagDomain N j g) (k : ℕ) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbu, hug⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj g hg
  have e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b := by
    unfold gramHead
    rw [← hug, gramOf_mul_of_preserves _ _ _ hu]
  rw [e]
  exact gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu

theorem flagDomain_open_and_minors : ∀ (N j : ℕ), j ≤ N →
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧
      ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k,
        (gramHead (sigForm N j) k g).det ≠ 0 :=
  fun N j hj => ⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicGroupLawGerm
section
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

def IsHolMarkingOn {n g : ℕ} {Λ : Type} [AddCommGroup Λ]
    (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ)
    (e : Λ → Λ → ℝ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) : Prop :=
  (∀ x, DifferentiableOn ℂ (fun b => P b x) U) ∧
    ∀ b ∈ U, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y

section
variable {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Countable Λ]
  {Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)} {Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ}
  {e : Λ → Λ → ℝ}

omit [Countable Λ] in
theorem IsHolMarkingOn.mono {U V : Set (Fin n → ℂ)} {P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (hVU : V ⊆ U) : IsHolMarkingOn Γ Q e V P :=
  ⟨fun x => (h.1 x).mono hVU, fun b hb => h.2 b (hVU hb)⟩

theorem IsHolMarkingOn.exists_twist {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), IsHolMarkingOn Γ Q e V R ∧
      ∀ b ∈ U ∩ V, R b = P b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ (U ∩ V) (hU.inter hV) hc hne P P'
    (fun x => (h.1 x).mono inter_subset_left) (fun x => (h'.1 x).mono inter_subset_right)
    (fun b hb => ⟨(h.2 b hb.1).1, (h'.2 b hb.2).1, by
      rw [(h.2 b hb.1).2.1, (h'.2 b hb.2).2.1]⟩)
  have hR : ∀ b ∈ U ∩ V, ∀ x, P' b (T.symm x) = P b x := fun b hb x => by
    rw [hT b hb, T.apply_symm_apply]
  refine ⟨fun b => (P' b).comp T.symm.toAddMonoidHom, ⟨fun x => h'.1 (T.symm x), ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨hi, hr, hq⟩ := h'.2 b hb
    refine ⟨hi.comp T.symm.injective, ?_, ?_⟩
    · rw [← hr]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨T.symm x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨T x, by simp⟩
    · intro x y
      obtain ⟨c, hc'⟩ := hne
      have h1 := (h.2 c hc'.1).2.2 x y
      have h2 := (h'.2 c hc'.2).2.2 (T.symm x) (T.symm y)
      rw [hR c hc' x, hR c hc' y, h1] at h2
      simpa using (hq (T.symm x) (T.symm y)).trans h2.symm
  · intro b hb
    ext1 x
    exact hR b hb x

theorem IsHolMarkingOn.exists_glue {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R, IsHolMarkingOn Γ Q e (U ∪ V) R := by
  classical
  obtain ⟨R, hR, hRP⟩ := h.exists_twist hU hV hc hne h'
  have eU : ∀ b ∈ U, (if b ∈ U then P b else R b) = P b := fun b hb => if_pos hb
  have eV : ∀ b ∈ V, (if b ∈ U then P b else R b) = R b := fun b hb => by
    by_cases hbU : b ∈ U
    · rw [if_pos hbU, hRP b ⟨hbU, hb⟩]
    · rw [if_neg hbU]
  refine ⟨fun b => if b ∈ U then P b else R b, fun x => ?_, ?_⟩
  · have d1 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) U :=
      (h.1 x).congr fun b hb => by rw [eU b hb]
    have d2 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) V :=
      (hR.1 x).congr fun b hb => by rw [eV b hb]
    rintro b (hb | hb)
    · exact ((d1 b hb).differentiableAt (hU.mem_nhds hb)).differentiableWithinAt
    · exact ((d2 b hb).differentiableAt (hV.mem_nhds hb)).differentiableWithinAt
  · rintro b (hb | hb)
    · simpa only [eU b hb] using h.2 b hb
    · simpa only [eV b hb] using hR.2 b hb

theorem IsHolMarkingOn.eq_of_eq_at {W : Set (Fin n → ℂ)} (hW : IsOpen W) (hc : IsPreconnected W)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e W P) (h' : IsHolMarkingOn Γ Q e W P')
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ W) (h0 : P b₀ = P' b₀) : ∀ b ∈ W, P b = P' b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ W hW hc ⟨b₀, hb₀⟩ P P' h.1 h'.1
    (fun b hb => ⟨(h.2 b hb).1, (h'.2 b hb).1, by rw [(h.2 b hb).2.1, (h'.2 b hb).2.1]⟩)
  have hid : ∀ x, T x = x := fun x => (h.2 b₀ hb₀).1 (by rw [← hT b₀ hb₀, h0])
  intro b hb
  ext1 x
  rw [hT b hb, hid]

theorem exists_marking_of_convex_family {B : Set (Fin n → ℂ)} {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (H : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P) :
    ∃ P, IsHolMarkingOn Γ Q e B P := by
  obtain ⟨U₀, hU₀, hC₀, -, hbU₀, -, P₀, hP₀⟩ := H b₀ hb₀
  have H' : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ R, IsHolMarkingOn Γ Q e U R ∧ R b₀ = P₀ b₀ := by
    intro b hb
    obtain ⟨U, hU, hC, hUB, h0, h1, P, hP⟩ := H b hb
    obtain ⟨R, hR, hRP⟩ := hP₀.exists_twist hU₀ hU (hC₀.inter hC).isPreconnected ⟨b₀, hbU₀, h0⟩ hP
    exact ⟨U, hU, hC, hUB, h0, h1, R, hR, hRP b₀ ⟨hbU₀, h0⟩⟩
  choose! U hU hC hUB h0 h1 R hR hRb using H'
  have key : ∀ b ∈ B, ∀ c ∈ U b, R c c = R b c := fun b hb c hcb => by
    have hc : c ∈ B := hUB b hb hcb
    exact ((hR c hc).mono inter_subset_left).eq_of_eq_at ((hU c hc).inter (hU b hb))
      ((hC c hc).inter (hC b hb)).isPreconnected ((hR b hb).mono inter_subset_right)
      ⟨h0 c hc, h0 b hb⟩ ((hRb c hc).trans (hRb b hb).symm) c ⟨h1 c hc, hcb⟩
  refine ⟨fun b => R b b, fun x b hb => ?_, fun b hb => (hR b hb).2 b (h1 b hb)⟩
  have hn := (hU b hb).mem_nhds (h1 b hb)
  have hev : (fun c => R c c x) =ᶠ[nhds b] fun c => R b c x := by
    filter_upwards [hn] with c hc
    rw [key b hb c hc]
  exact (((hR b hb).1 x b (h1 b hb)).differentiableAt hn).congr_of_eventuallyEq hev
    |>.differentiableWithinAt

theorem exists_marking_tube {B : Set (Fin n → ℂ)} (hconv : Convex ℝ B)
    (H : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e N P)
    {a b : Fin n → ℂ} (ha : a ∈ B) (hb : b ∈ B) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ a ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P := by
  let γ : ℝ →ᵃ[ℝ] (Fin n → ℂ) := AffineMap.lineMap a b
  have hγ : Continuous γ := by
    have : (γ : ℝ → Fin n → ℂ) = fun t => t • (b - a) + a :=
      funext fun t => AffineMap.lineMap_apply_module' a b t
    rw [this]
    fun_prop
  have hγ0 : γ 0 = a := AffineMap.lineMap_apply_zero a b
  have hγ1 : γ 1 = b := AffineMap.lineMap_apply_one a b
  have hmem : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ B := fun r hr =>
    hconv.segment_subset ha hb (by rw [segment_eq_image_lineMap]; exact ⟨r, hr, rfl⟩)
  let ι := {N : Set (Fin n → ℂ) // IsOpen N ∧ N ⊆ B ∧ ∃ P, IsHolMarkingOn Γ Q e N P}
  let c : ι → Set unitInterval := fun N => (fun s : unitInterval => γ s) ⁻¹' N.1
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hcov⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := c) (fun N => N.2.1.preimage (hγ.comp continuous_subtype_val)) (fun s _ => by
      obtain ⟨N, h1, h2, h3, h4⟩ := H _ (hmem s s.2)
      exact mem_iUnion.2 ⟨⟨N, h1, h3, h4⟩, h2⟩)
  have claim : ∀ k, ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (γ '' Icc 0 (t k : ℝ)) ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e (Metric.thickening δ (γ '' Icc 0 (t k : ℝ))) P := by
    intro k
    induction k with
    | zero =>
      obtain ⟨N, hN, haN, hNB, P, hP⟩ := H a ha
      have hsub : γ '' Icc 0 (t 0 : ℝ) ⊆ N := by
        rintro _ ⟨r, hr, rfl⟩
        have hr0 : r = 0 := le_antisymm (by simpa [ht0] using hr.2) hr.1
        rw [hr0, hγ0]
        exact haN
      obtain ⟨δ, hδ, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hN hsub
      exact ⟨δ, hδ, hth.trans hNB, P, hP.mono hth⟩
    | succ k ih =>
      obtain ⟨δ₁, hδ₁, hB₁, P₁, hP₁⟩ := ih
      obtain ⟨N, hN⟩ := hcov k
      obtain ⟨hNo, hNB, P₂, hP₂⟩ := N.2
      have hle : (t k : ℝ) ≤ t (k + 1) := hmono (Nat.le_succ k)
      have h0 : (0 : ℝ) ≤ t k := (t k).2.1
      have hsub : γ '' Icc (t k : ℝ) (t (k + 1)) ⊆ N.1 := by
        rintro _ ⟨r, hr, rfl⟩
        have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hr.1, hr.2.trans (t (k + 1)).2.2⟩
        exact hN (show (⟨r, hr'⟩ : unitInterval) ∈ Icc (t k) (t (k + 1)) from ⟨hr.1, hr.2⟩)
      obtain ⟨δ₂, hδ₂, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hNo hsub
      have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      have hA : Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ⊆
          Metric.thickening δ₁ (γ '' Icc 0 (t k : ℝ)) :=
        Metric.thickening_mono (min_le_left _ _) _
      have hC : Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) ⊆ N.1 :=
        (Metric.thickening_mono (min_le_right _ _) _).trans hth
      have hKs : γ '' Icc 0 (t (k + 1) : ℝ) =
          γ '' Icc 0 (t k : ℝ) ∪ γ '' Icc (t k : ℝ) (t (k + 1)) := by
        rw [← image_union, Icc_union_Icc_eq_Icc h0 hle]
      have hconvA := ((convex_Icc (0 : ℝ) (t k)).affine_image γ).thickening (min δ₁ δ₂)
      have hconvC := ((convex_Icc (t k : ℝ) (t (k + 1))).affine_image γ).thickening (min δ₁ δ₂)
      have hpt : γ (t k) ∈ Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ∩
          Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) :=
        ⟨Metric.self_subset_thickening hδ _ ⟨_, ⟨h0, le_rfl⟩, rfl⟩,
          Metric.self_subset_thickening hδ _ ⟨_, ⟨le_rfl, hle⟩, rfl⟩⟩
      obtain ⟨R, hR⟩ := (hP₁.mono hA).exists_glue (P' := P₂) Metric.isOpen_thickening
        Metric.isOpen_thickening (hconvA.inter hconvC).isPreconnected ⟨_, hpt⟩ (hP₂.mono hC)
      refine ⟨min δ₁ δ₂, hδ, ?_, R, ?_⟩
      · rw [hKs, Metric.thickening_union]
        exact union_subset (hA.trans hB₁) (hC.trans hNB)
      · rw [hKs, Metric.thickening_union]
        exact hR
  obtain ⟨δ, hδ, hδB, P, hP⟩ := claim m
  have htm : (t m : ℝ) = 1 := by rw [hm m le_rfl]; rfl
  rw [htm] at hδB hP
  exact ⟨_, Metric.isOpen_thickening, ((convex_Icc (0 : ℝ) 1).affine_image γ).thickening δ, hδB,
    Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩,
    Metric.self_subset_thickening hδ _ ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩, P, hP⟩

end

theorem exists_global_marking_of_local : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → Convex ℝ B → ∀ (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (e : Λ → Λ → ℝ), (∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) N) ∧ ∀ b ∈ N, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y) → ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y := by
  intro n g Λ _ _ B _ hconv Γ Q e H
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨fun _ => 0, fun x => by simp, by simp⟩
  · have H' : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
        ∃ P, IsHolMarkingOn Γ Q e N P := fun b hb => by
      obtain ⟨N, h1, h2, h3, P, h4, h5⟩ := H b hb
      exact ⟨N, h1, h2, h3, P, h4, h5⟩
    obtain ⟨P, hP⟩ := exists_marking_of_convex_family hb₀
      (fun b hb => exists_marking_tube hconv H' hb₀ hb)
    exact ⟨P, hP.1, hP.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem harmonicAt_update_of_levi_eq_zero :
    ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O →
      (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i,
        InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  intro n φ O hO hφ hl z hz i
  set e : Fin n → ℂ := Pi.single i 1 with he
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  set z0 : Fin n → ℂ := Function.update z i 0 with hz0
  have hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e := by
    intro t
    funext j
    by_cases h : j = i
    · subst h
      simp [hz0, he]
    · simp [hz0, he, h]
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z0
  have hcont : Continuous (fun t : ℂ => z0 + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O) := hO.preimage hcont
  have hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O := by
    show z0 + z i • e ∈ O
    rw [← hupd]
    simpa using hz
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0 := by
    intro t ht
    have hy : z0 + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  rw [show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from
    funext fun t => by rw [hupd]]
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i) := by
      have : ContDiff ℝ 2 (fun t : ℂ => z0 + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ hzU).comp (z i) hA
  · filter_upwards [hU.mem_nhds hzU] with t ht
    simpa using hlap t ht

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChart
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_eq_zero_of_compatChart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ →
    IsOpen U → A.SmoothOn U g →
    (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w,
      levi (g ∘ (A.chart j).symm) y w = 0) →
    ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  intro e X _ A ψ U g hψ hU hg hA z hz hzU w
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hzs : z ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := ⟨hz, hj⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart j).open_source
  have hτ : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) z := (hψ j).2 z hzs
  have hEq : g ∘ ⇑ψ.symm =ᶠ[𝓝 z] (g ∘ ⇑(A.chart j).symm) ∘ (⇑(A.chart j) ∘ ⇑ψ.symm) := by
    filter_upwards [hopen.mem_nhds hzs] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy.2]
  have hcz : (⇑(A.chart j) ∘ ⇑ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hzU
  have hopen2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  have hsm : ContDiffAt ℝ 2 (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) z) :=
    ((hg j).contDiffAt (hopen2.mem_nhds hcz)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  rw [levi_congr hEq w, levi_comp w hτ hsm]
  exact hA j _ hcz _

end GlobalTheory.CompanionTheory.LeviChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransformStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_gram_subharmonic : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | exact GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightMapAntisymmetricDeltaIdentityStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_product_weight_positive : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBoundStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | exact GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame <;> assumption)
end

