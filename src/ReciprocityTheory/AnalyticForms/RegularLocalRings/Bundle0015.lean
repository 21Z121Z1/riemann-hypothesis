import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0008
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LiftChartIdeal

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem chartIdeal_le_ptIdealOf {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    chartIdeal P p ≤ ptIdealOf z := fun h hh => by
  show h ∈ RingHom.ker (MvPolynomial.eval z : MvPolynomial (Σ k, ι k) ℂ →+* ℂ)
  exact RingHom.mem_ker.2 (hz h hh)

theorem ringKrullDim_locAt_chart_le {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    ringKrullDim (locAt (chartIdeal P p) z) ≤ e := by
  have hle := chartIdeal_le_ptIdealOf hz
  rw [ringKrullDim_locAt _ z hle]
  have : ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  refine ringKrullDim_le_of_forall_quotient _ fun 𝔓 h𝔓 => ?_
  have : (𝔓.comap (Ideal.Quotient.mk (chartIdeal P p))).IsPrime := Ideal.comap_isPrime _ _
  have hI : chartIdeal P p ≤ 𝔓.comap (Ideal.Quotient.mk (chartIdeal P p)) := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact 𝔓.zero_mem
  refine le_trans ?_ (ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p _ hI)
  let g : MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔓.comap (Ideal.Quotient.mk (chartIdeal P p)) →+*
      (MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p) ⧸ 𝔓 :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk 𝔓).comp (Ideal.Quotient.mk _))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  refine ringKrullDim_le_of_surjective g ?_
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

set_option maxHeartbeats 600000 in

theorem le_ringKrullDim_locAt_chart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    (e : WithBot ℕ∞) ≤ ringKrullDim (locAt (chartIdeal P p) z) := by
  have hIm : chartIdeal P p ≤ ptIdealOf z := chartIdeal_le_ptIdealOf hz
  have hPm : P ≤ ptIdealOf z := le_sup_left.trans hIm
  have := ptIdealOf_isMaximal z
  obtain ⟨Q, hQmin, hQm⟩ := Ideal.exists_minimalPrimes_le hPm
  have hQp : Q.IsPrime := hQmin.1.1
  have hPQ : P ≤ Q := hQmin.1.2
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) := Ideal.Quotient.isDomain Q
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q) (Ideal.Quotient.mkₐ_surjective ℂ Q)
  obtain ⟨s, hsd, hst⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Σ k, ι k) ℂ ⧸ Q)
  have hs : s = e + Fintype.card K := by
    have h := hdim Q hQmin
    rw [hsd] at h
    exact_mod_cast h
  have hmQ : ((ptIdealOf z).map (Ideal.Quotient.mk Q)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective (ptIdealOf_isMaximal z) with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk Q 1 ∈ (ptIdealOf z).map (Ideal.Quotient.mk Q) := by
        rw [h]; exact Submodule.mem_top
      exact (ptIdealOf_isMaximal z).ne_top
        ((Ideal.eq_top_iff_one _).mpr ((Ideal.mem_quotient_iff_mem hQm).mp h1))
    · exact h
  have hhtQ : ((ptIdealOf z).map (Ideal.Quotient.mk Q)).height = ((e + Fintype.card K : ℕ) : ℕ∞) := by
    rw [← hs]
    exact ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field (K := ℂ) s hst _
  have hdQ : ringKrullDim (locAt Q z) = (((e + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_locAt Q z hQm, hhtQ]
  have hPQd : ringKrullDim (locAt Q z) ≤ ringKrullDim (locAt P z) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hPQ))
      (Ideal.Quotient.factor_surjective _)

  let J : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
    Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))
  obtain ⟨sset, hsset⟩ : ∃ s : Set (MvPolynomial (Σ k, ι k) ℂ ⧸ P), s = Ideal.Quotient.mk P ''
      Set.range (fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) := ⟨_, rfl⟩
  have hmP : ((ptIdealOf z).map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPm)
  have hsub : sset ⊆ (ptIdealOf z).map (Ideal.Quotient.mk P) := by
    rw [hsset]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact Ideal.mem_map_of_mem _ (hIm (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)))
  have hH := Ideal.height_le_height_add_encard_of_subset sset hsub
  have hspan : Ideal.span sset = J.map (Ideal.Quotient.mk P) := by
    rw [hsset, Ideal.map_span]
  let eq2 : (MvPolynomial (Σ k, ι k) ℂ ⧸ P) ⧸ Ideal.span sset ≃+* MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup P J)
  have hcomp : (eq2 : _ →+* _).comp ((Ideal.Quotient.mk (Ideal.span sset)).comp (Ideal.Quotient.mk P)) =
      Ideal.Quotient.mk (chartIdeal P p) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, eq2, RingEquiv.coe_toRingHom]
    exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk P J a
  have hht : ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height =
      (((ptIdealOf z).map (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk (Ideal.span sset))).height := by
    have hmap : (((ptIdealOf z).map (Ideal.Quotient.mk P)).map
        (Ideal.Quotient.mk (Ideal.span sset))).map eq2 =
        (ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p)) := by
      have h : (((ptIdealOf z).map (Ideal.Quotient.mk P)).map
          (Ideal.Quotient.mk (Ideal.span sset))).map (eq2 : _ →+* _) =
          (ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p)) := by
        rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hcomp]
      exact h
    rw [← hmap, RingEquiv.height_map]
  have henc : sset.encard ≤ Fintype.card K := by
    rw [hsset]
    refine (Set.encard_image_le (Ideal.Quotient.mk P) _).trans ?_
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  have h1 : ((e + Fintype.card K : ℕ) : ℕ∞) ≤ ((ptIdealOf z).map (Ideal.Quotient.mk P)).height := by
    have h := hPQd
    rw [hdQ, ringKrullDim_locAt P z hPm] at h
    exact_mod_cast h
  have h2 : ((ptIdealOf z).map (Ideal.Quotient.mk P)).height ≤
      ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height + Fintype.card K := by
    rw [hht]
    exact hH.trans (by gcongr)
  have h3 : (e : ℕ∞) ≤ ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).height := by
    have h4 := h1.trans h2
    rw [Nat.cast_add, add_comm, add_comm _ (Fintype.card K : ℕ∞)] at h4
    exact ENat.addLECancellable_of_ne_top (ENat.natCast_ne_top _) h4
  rw [ringKrullDim_locAt _ z hIm]
  exact_mod_cast h3

theorem ringKrullDim_locAt_chart (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P)
    (e : ℕ) (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    ringKrullDim (locAt (chartIdeal P p) z) = e :=
  le_antisymm (ringKrullDim_locAt_chart_le hP e hdim p z hz) (le_ringKrullDim_locAt_chart e hdim p z hz)

set_option maxHeartbeats 400000 in

theorem isRegularLocalRing_locAt_chart (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {t : ℕ} (G : Fin t → MvPolynomial (Σ k, ι k) ℂ) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (hspan : Ideal.span (Set.range G) = P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0)
    (a : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Fin t)
    (b : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Σ k, ι k)
    (hab : eval z (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ≠ 0) :
    IsRegularLocalRing (locAt (chartIdeal P p) z) := by
  classical
  have hP : IsMultiHomogIdeal P := ⟨Set.range G, by rintro _ ⟨i, rfl⟩; exact hG i, hspan.symm⟩
  have hGP : ∀ i, G i ∈ P := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hGI : ∀ i, G i ∈ chartIdeal P p := fun i => Ideal.mem_sup_left (hGP i)
  have hXI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p := fun k =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  have hz1 : ∀ k, z ⟨k, p k⟩ = 1 := fun k => by
    have h := hz _ (hXI k)
    simpa [sub_eq_zero] using h
  obtain ⟨hloc, hnoeth⟩ := locAt_isLocalRing_isNoetherian (chartIdeal P p) z hz
  have hcot := finrank_cotangentSpace_locAt (chartIdeal P p) z
  have hd := ringKrullDim_locAt_chart P hP e hdim p z hz
  let grad : MvPolynomial (Σ k, ι k) ℂ → (Σ k, ι k) → ℂ := fun h j => eval z (pderiv j h)
  let v : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) ⊕ K → (Σ k, ι k) → ℂ :=
    Sum.elim (fun i => grad (G (a i))) (fun k => grad (X ⟨k, p k⟩ - 1))
  let lam : K → ((Σ k, ι k) → ℂ) →ₗ[ℂ] ℂ := fun k =>
    { toFun := fun w => ∑ q, (blockWt k q : ℂ) * (z q * w q)
      map_add' := fun w w' => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hlam : ∀ k w, lam k w = ∑ q, (blockWt k q : ℂ) * (z q * w q) := fun _ _ => rfl
  have hlamG : ∀ k i, lam k (grad (G i)) = 0 := by
    intro k i
    obtain ⟨dg, hdg⟩ := hG i
    rw [hlam]
    exact (sum_blockWt_eval hdg k z).trans (by rw [hz _ (hGI i), mul_zero])
  have hlamX : ∀ k k', lam k (grad (X ⟨k', p k'⟩ - 1)) = if k' = k then 1 else 0 := by
    intro k k'
    rw [hlam, Finset.sum_eq_single ⟨k', p k'⟩]
    · simp [grad, blockWt, hz1]
    · intro q _ hq
      simp [grad, Ne.symm hq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hK : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (lam k) hg
      simp only [map_add, map_sum, map_smul, map_zero, smul_eq_mul, v, Sum.elim_inl, Sum.elim_inr,
        hlamG, hlamX, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h
    have hg2 : ∑ i, g (Sum.inl i) • grad (G (a i)) = 0 := by
      simpa only [v, Sum.elim_inl, Sum.elim_inr, hK, zero_smul, Finset.sum_const_zero, add_zero]
        using hg
    let M : Matrix (Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) (Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) ℂ := Matrix.of fun i j => eval z (pderiv (b j) (G (a i)))
    have hM : M.det ≠ 0 := by
      rw [RingHom.map_det] at hab
      convert hab using 2
      ext i j
      simp [M, RingHom.mapMatrix_apply]
    have hvec : Matrix.vecMul (fun i => g (Sum.inl i)) M = 0 := by
      funext j
      have h := congrFun hg2 (b j)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, grad] at h
      simpa only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply] using h
    have hFin : ∀ i, g (Sum.inl i) = 0 := by
      intro i
      by_contra hi
      exact hM (Matrix.exists_vecMul_eq_zero_iff.mp
        ⟨fun i => g (Sum.inl i), fun h => hi (congrFun h i), hvec⟩)
    rintro (i | k)
    · exact hFin i
    · exact hK k
  have hmem : ∀ x, v x ∈ jacSpanAt (chartIdeal P p) z := by
    rintro (i | k)
    · exact Submodule.subset_span ⟨G (a i), hGI (a i), rfl⟩
    · exact Submodule.subset_span ⟨_, hXI k, rfl⟩
  have hrank : (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) + Fintype.card K ≤ Module.finrank ℂ (jacSpanAt (chartIdeal P p) z) := by
    let v' : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) ⊕ K → jacSpanAt (chartIdeal P p) z := fun x => ⟨v x, hmem x⟩
    have hv' : LinearIndependent ℂ v' := LinearIndependent.of_comp (jacSpanAt _ _).subtype hv
    simpa using hv'.fintype_card_le_finrank
  have hcotle : Module.finrank (ResidueField (locAt (chartIdeal P p) z))
      (CotangentSpace (locAt (chartIdeal P p) z)) ≤ e := by
    omega
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]
  exact_mod_cast hcotle

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ContinuousOnOfCharts
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem sep_of_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U) {x y : X} (hx : x ∈ U)
    (hy : y ∈ U) (hne : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
  obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ := t2_separation hne
  refine ⟨U ∩ f ⁻¹' a, U ∩ f ⁻¹' b, hf.isOpen_inter_preimage hU ha, hf.isOpen_inter_preimage hU hb,
    ⟨hx, hxa⟩, ⟨hy, hyb⟩, ?_⟩
  exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hab hz.2 hz'.2

def blkNorm (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : ℝ :=
  Complex.normSq (z q) / ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩)

theorem blkNorm_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) :
    blkNorm z q = blkNorm z' q := by
  obtain ⟨a, ha, rfl⟩ := h
  have hq : Complex.normSq (a q.1) ≠ 0 := by simpa using ha q.1
  simp only [blkNorm, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem blkNorm_ne_zero_iff (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : blkNorm z q ≠ 0 ↔ z q ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [blkNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (z q) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (z q) ≤ ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩) :=
      Finset.single_le_sum (f := fun j => Complex.normSq (z ⟨q.1, j⟩))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ q.2)
    exact (div_pos h1 (h1.trans_le h2)).ne'

def vecNorm {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : ℝ :=
  Complex.normSq (v l) / ∑ k, Complex.normSq (v k)

theorem vecNorm_smul {m : ℕ} {v v' : Fin m → ℂ} (a : ℂ) (ha : a ≠ 0) (h : ∀ k, v k = a * v' k)
    (l : Fin m) : vecNorm v l = vecNorm v' l := by
  have hq : Complex.normSq a ≠ 0 := by simpa using ha
  simp only [vecNorm, h, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem vecNorm_ne_zero_iff {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : vecNorm v l ≠ 0 ↔ v l ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [vecNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (v l) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (v l) ≤ ∑ k, Complex.normSq (v k) :=
      Finset.single_le_sum (f := fun k => Complex.normSq (v k))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ l)
    exact (div_pos h1 (h1.trans_le h2)).ne'

namespace WData

attribute [local instance] WData.lft

variable (w : WData P D hP)

theorem coord_eq_of_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.coord c x = (w.pres c.1 c.2).coord x.1 hx :=
  dif_pos hx

theorem continuousOn_coord (c : w.Idx) : ContinuousOn (w.coord c) (w.src c) := by
  rw [continuousOn_iff']
  intro O hO
  refine ⟨w.src c ∩ w.coord c ⁻¹' O, TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

theorem continuousOn_of_charts {Y : Type*} [TopologicalSpace Y] (U : Set w.M) (f : w.M → Y)
    (h : ∀ x ∈ U, ∃ c, x ∈ w.src c ∧ w.src c ⊆ U ∧ ∃ F : (Fin (w.pres c.1 c.2).n → ℂ) → Y,
      Continuous F ∧ ∀ y ∈ w.src c, f y = F (w.coord c y)) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨c, hxc, -, F, hF, hfF⟩ := h x hx
  have h1 : ContinuousOn (F ∘ w.coord c) (w.src c) := hF.comp_continuousOn (w.continuousOn_coord c)
  have h2 : ContinuousOn f (w.src c) := h1.congr fun y hy => hfF y hy
  exact (h2.continuousAt ((w.isOpen_alt_bis c).mem_nhds hxc)).continuousWithinAt

def lv (c : w.Idx) (x : w.M) : (Σ k, ι k) → ℂ := fun q => eval (w.coord c x) (w.lift c q)

theorem lv_self (c : w.Idx) (x : w.M) (k : K) : w.lv c x ⟨k, c.1 k⟩ = 1 := by
  simp [lv, lift]

theorem one_le_sum_lv (c : w.Idx) (x : w.M) (k : K) :
    1 ≤ ∑ j : ι k, Complex.normSq (w.lv c x ⟨k, j⟩) := by
  have h2 := Finset.single_le_sum (f := fun j => Complex.normSq (w.lv c x ⟨k, j⟩))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ (c.1 k))
  simp only [lv_self, map_one] at h2
  exact h2

def ch (x : w.M) : w.Idx := (w.cover x).choose

theorem mem_ch (x : w.M) : x ∈ w.src (w.ch x) := (w.cover x).choose_spec

def blk (q : Σ k, ι k) (x : w.M) : ℝ := blkNorm (w.lv (w.ch x) x) q

theorem blk_eq (q : Σ k, ι k) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.blk q x = blkNorm (w.lv c x) q :=
  blkNorm_of_sameOrbit (w.compat (w.ch x) c x ⟨w.mem_ch x, hx⟩) q

theorem continuous_blk (q : Σ k, ι k) : Continuous (w.blk q) := by
  rw [← continuousOn_univ]
  refine w.continuousOn_of_charts _ _ fun x _ => ⟨w.ch x, w.mem_ch x, Set.subset_univ _, ?_⟩
  set c := w.ch x
  refine ⟨fun v => Complex.normSq (eval v (w.lift c q)) /
    max 1 (∑ j : ι q.1, Complex.normSq (eval v (w.lift c ⟨q.1, j⟩))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _)).div
      (continuous_const.max (continuous_finsetSum _ fun j _ =>
        Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.lv c y q) / max 1 (∑ j : ι q.1, Complex.normSq (w.lv c y ⟨q.1, j⟩))
    rw [w.blk_eq q c y hy, blkNorm, max_eq_right (w.one_le_sum_lv c y q.1)]

def tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) : Fin (w.m p) → ℂ :=
  fun k => w.coord ⟨p, i⟩ x (w.yt p i k)

theorem tv_eq_val (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩)
    (k : Fin (w.m p)) : w.tv p i x k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hx := by
  have h := (w.pres p i).eval_coord_eq_val x.1 hx x.2 (X (w.yt p i k))
  rw [eval_X, w.sec_yt] at h
  rw [tv, w.coord_eq_of_mem ⟨p, i⟩ x hx]
  exact h

theorem val_t_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) :
    val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi =
      val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hj * val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi := by
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨hi, hj⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) ((w.pres p i).V ⊓ (w.pres p j).V) x.1 hij x.2
  have h := congrArg φ (w.t_cocycle p i j k)
  rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h
  exact h.symm

theorem val_t_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M)
    (hi : x ∈ w.src ⟨p, i⟩) :
    val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  have h1 := val_eq_zero_iff (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi x.2
  have h2 := Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := w.W) x.1 hi (w.t p i j)
  have h3 : x.1 ∈ w.W.basicOpen (w.t p i j) ↔ x ∈ w.src ⟨p, j⟩ := by
    rw [← w.inter p i j, TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
  exact (h1.not.trans h2).trans h3

theorem tv_self (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x i = 1 := by
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) (w.pres p i).V x.1 hx x.2
  rw [w.tv_eq_val p i x hx, ← hφ, w.t_self, map_one]

theorem tv_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x j ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  rw [w.tv_eq_val p i x hi]
  exact w.val_t_ne_zero_iff p i j x hi

theorem tv_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) : w.tv p i x k = w.tv p i x j * w.tv p j x k := by
  rw [w.tv_eq_val p i x hi, w.tv_eq_val p i x hi, w.tv_eq_val p j x hj, w.val_t_mul p i j x hi hj k,
    mul_comm]

theorem one_le_sum_tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    1 ≤ ∑ k, Complex.normSq (w.tv p i x k) := by
  have h2 := Finset.single_le_sum (f := fun k => Complex.normSq (w.tv p i x k))
    (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  simp only [w.tv_self p i x hx, map_one] at h2
  exact h2

def overP (p : (k : K) → ι k) : Set w.M := {x | ∃ i, x ∈ w.src ⟨p, i⟩}

theorem isOpen_overP (p : (k : K) → ι k) : IsOpen (w.overP p) := by
  have h : w.overP p = ⋃ i, w.src ⟨p, i⟩ := by
    ext x
    simp [overP]
  rw [h]
  exact isOpen_iUnion fun i => w.isOpen_alt_bis _

open Classical in

def fib (p : (k : K) → ι k) (l : Fin (w.m p)) (x : w.M) : ℝ :=
  if h : ∃ i, x ∈ w.src ⟨p, i⟩ then vecNorm (w.tv p h.choose x) l else 0

theorem fib_eq (p : (k : K) → ι k) (l : Fin (w.m p)) (i : Fin (w.m p)) (x : w.M)
    (hx : x ∈ w.src ⟨p, i⟩) : w.fib p l x = vecNorm (w.tv p i x) l := by
  have h : ∃ i, x ∈ w.src ⟨p, i⟩ := ⟨i, hx⟩
  rw [fib, dif_pos h]
  exact vecNorm_smul _ ((w.tv_ne_zero_iff p _ i x h.choose_spec).mpr hx)
    (fun k => w.tv_mul p _ i x h.choose_spec hx k) l

theorem continuousOn_fib (p : (k : K) → ι k) (l : Fin (w.m p)) :
    ContinuousOn (w.fib p l) (w.overP p) := by
  refine w.continuousOn_of_charts _ _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨p, i⟩, hi, fun y hy => ⟨i, hy⟩, ?_⟩
  refine ⟨fun v => Complex.normSq (v (w.yt p i l)) /
    max 1 (∑ k, Complex.normSq (v (w.yt p i k))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (continuous_apply _)).div
      (continuous_const.max (continuous_finsetSum _ fun k _ =>
        Complex.continuous_normSq.comp (continuous_apply _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.tv p i y l) / max 1 (∑ k, Complex.normSq (w.tv p i y k))
    rw [w.fib_eq p l i y hy, vecNorm, max_eq_right (w.one_le_sum_tv p i y hy)]

end WData

end

end ReciprocityTheory.AnForm.R
end

