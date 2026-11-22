import Mathlib
import Formalism.HermitianLattices.Bundle0001
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.SuccessiveMinima.MinkowskiIIUpper

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

private theorem mem_dual_iff_hermitian_lattices {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem dualOrthSum : DualOrthSum := by
  intro R K V _ _ _ _ _ _ _ _ h V₁ V₂ hc h12 h21 L₁ L₂ hL₁ hL₂
  apply le_antisymm
  · intro x hx
    rw [mem_dual_iff_hermitian_lattices] at hx
    have htop : x ∈ V₁ ⊔ V₂ := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp htop
    refine Submodule.mem_sup.mpr ⟨x₁, Submodule.mem_inf.mpr ⟨?_, hx₁⟩,
      x₂, Submodule.mem_inf.mpr ⟨?_, hx₂⟩, rfl⟩
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₂ = 0 := h12 y (hL₁ hy) x₂ hx₂
      have hm := hx y (Submodule.mem_sup_left hy)
      rwa [map_add, e, add_zero] at hm
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₁ = 0 := h21 y (hL₂ hy) x₁ hx₁
      have hm := hx y (Submodule.mem_sup_right hy)
      rwa [map_add, e, zero_add] at hm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, LinearMap.add_apply, h21 y₂ (hL₂ hy₂) x hxV, add_zero]
      exact hxd y₁ hy₁
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, LinearMap.add_apply, h12 y₁ (hL₁ hy₁) x hxV, zero_add]
      exact hxd y₂ hy₂

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
section
namespace Formalism.HermitianLatticesTheory

theorem finIntermediate : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]

end Formalism.HermitianLatticesTheory
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusBasic_gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  rw [isomAct_mem_gmap]
  first
  | rfl
  | simp
  | exact Iff.rfl

theorem genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by
  ext x
  simp only [isomAct_mem_gmap]
  rfl

theorem genusBasic_gmap_inv (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)

theorem genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ r hx

theorem genusBasic_hsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h v (r • w) = algebraMap R K r * h v w := by
  rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]

theorem genusBasic_hsmul_left (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h (r • v) w = algebraMap R K (locBasic_sigma hinj hstar r) * h v w := by
  rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    locBasic_sigma_spec, starRingEnd_apply]

theorem genusBasic_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨hx1, hx2⟩ := hx
    refine Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)
    have e : t = x := hinj (by rw [ht, locBasic_sigma_spec, star_star])
    rw [e]
    exact hx1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem genusBasic_hS (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs

theorem genusBasic_lg {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx

theorem genusBasic_common (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w

theorem genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _

theorem genusBasic_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩

theorem genusBasic_int (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring

theorem genusBasic_dual_le (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem

end SlopeTestRemainingChoices

theorem genusBasic : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem isomOfTrace : IsomOfTrace := by
  intro K V _ _ _ _ _ h g hg
  show ∀ x y, h (g x) (g y) = h x y
  intro x y
  by_contra hne
  have hd : h (g x) (g y) - h x y ≠ 0 := sub_ne_zero.mpr hne
  have key := hg x ((h (g x) (g y) - h x y)⁻¹ • y)
  simp only [map_smul, smul_eq_mul] at key
  have h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0 := by
    rw [mul_sub, map_sub, key, sub_self]
  rw [inv_mul_cancel₀ hd] at h0
  have h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ) := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1] at h0
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact absurd h0 (by exact_mod_cast hpos.ne')

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
section
open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.HermitianLatticesTheory

private lemma shortVectors_norm_le {N : ℕ} {t : ℝ} (ht : 0 < t) {u : EuclideanSpace ℝ (Fin N)}
    (hu : u ∈ t • closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) : ‖u‖ ≤ t := by
  obtain ⟨v, hv, rfl⟩ := hu
  rw [mem_closedBall_zero_iff] at hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_le_of_le_one_right ht.le hv

private lemma shortVectors_prod_ge {n : ℕ} {c : ℝ} (hc : 0 < c) (lam : Fin n → ℝ)
    (hlow : ∀ i, c ≤ lam i) (j : Fin n) : lam j * c ^ (n - 1) ≤ ∏ i, lam i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ j)]
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have h1 : c ^ (n - 1) ≤ ∏ i ∈ Finset.univ.erase j, lam i := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => hc.le) (fun i _ => hlow i)
  have hj : 0 ≤ lam j := le_trans hc.le (hlow j)
  exact mul_le_mul_of_nonneg_left h1 hj

private lemma shortVectors_vol_pos (N : ℕ) :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
  show 0 < (volume (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne' measure_closedBall_lt_top.ne

theorem shortVectors : ShortVectors := by
  intro N c C hc
  refine ⟨2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C /
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)), ?_⟩
  intro Λ _ _ hmin hcov
  have hK : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := isCompact_closedBall 0 1
  have hconv : Convex ℝ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := convex_closedBall 0 1
  have hsym : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1,
      -x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    rwa [norm_neg]
  have hint : (0 : EuclideanSpace ℝ (Fin N)) ∈
      interior (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact mem_ball_self one_pos
  obtain ⟨v, hli, hvL, hvK, hpos, -, -⟩ := Formalism.FN.existsSuccessiveMinimaVectors Λ _ hK hconv hsym hint
  have hM := Formalism.FN.minkowskiIIUpper (volume : Measure (EuclideanSpace ℝ (Fin N))) Λ _
    hK hconv hsym hint
  have hV := shortVectors_vol_pos N
  have hlow : ∀ i : Fin (finrank ℝ (EuclideanSpace ℝ (Fin N))), c ≤ Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
      ((i : ℕ) + 1) := by
    intro i
    exact le_trans (hmin _ (hvL i) (hli.ne_zero i)) (shortVectors_norm_le (hpos i) (hvK i))
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  refine ⟨fun i => v (Fin.cast hN.symm i), fun i => hvL _,
    hli.comp _ (Fin.cast_injective _), fun i => ?_⟩
  refine le_trans (shortVectors_norm_le (hpos _) (hvK _)) ?_
  have hcp : 0 < c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1) := pow_pos hc _
  rw [le_div_iff₀ (mul_pos hV hcp)]
  have h1 := shortVectors_prod_ge hc
    (fun i => Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) ((i : ℕ) + 1))
    hlow (Fin.cast hN.symm i)
  have h2 : (2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * ZLattice.covolume Λ ≤
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C :=
    mul_le_mul_of_nonneg_left hcov (by positivity)
  have h3 := mul_le_mul_of_nonneg_left h1 hV.le
  calc _ = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        (Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
          ((Fin.cast hN.symm i : ℕ) + 1) * c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)) := by
        ring
    _ ≤ _ := h3
    _ ≤ _ := hM
    _ ≤ _ := h2

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.ThetaBasic
section
open Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem thetaBasic_trace_star {K : Type*} [Field K] [NumberField K] [StarRing K] (a : K) :
    Algebra.trace ℚ K (star a) = Algebra.trace ℚ K a := by
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut K))
    (fun x => ((starRingAut : K ≃+* K).toRingHom.map_rat_algebraMap x))
  exact Algebra.trace_eq_of_algEquiv e a

def thetaBasic_eqv {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) : L ≃ gmap g L where
  toFun x := ⟨g x, Submodule.mem_map_of_mem x.2⟩
  invFun y := ⟨g.symm y, by
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.2
    have hz' : g z = (y : V) := hzy
    rw [← hz', LinearEquiv.symm_apply_apply]
    exact hz⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem thetaBasic_eqv_apply {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) (x : L) :
    ((thetaBasic_eqv g L x : gmap g L) : V) = g x := rfl

theorem thetaBasic : ThetaBasic := by
  intro K V _ _ _ _ _ _ _ h hh L γ τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    unfold thetaL
    refine Eq.trans ?_ ((Equiv.addRight (⟨l, hl⟩ : L)).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    rw [show γ + l + (x : V) = γ + ((x : V) + l) by abel]
  · unfold thetaL
    refine Eq.trans ?_ ((Equiv.neg L).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, Submodule.coe_neg]
    rw [show -γ + (x : V) = -(γ + -(x : V)) by abel]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  · intro g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaL
    rw [← (thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    rw [thetaBasic_eqv_apply, ← map_add, hg']
  · intro hev hdual
    unfold thetaL
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    obtain ⟨m, hm⟩ := hev x x.2
    obtain ⟨n, hn⟩ := hdual x x.2
    have h1 : h (x : V) γ = star (h γ x) := (hh.eq γ x).symm
    have hx : Algebra.trace ℚ K (h (γ + x) (γ + x)) =
        Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) := by
      simp only [map_add, LinearMap.add_apply, h1, thetaBasic_trace_star, hn, hm]
      ring
    rw [hx, ← Complex.exp_add]
    set T0 : ℂ := ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)
    have : (Real.pi : ℂ) * Complex.I * (τ + 1) * (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)
        = (Real.pi * Complex.I * T0 + Real.pi * Complex.I * τ *
          (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)) +
          ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [T0]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro n γs T g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaN
    rw [← (Equiv.piCongrRight fun _ : Fin n => thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, thetaBasic_eqv_apply, ← map_add, hg']
  · intro T
    unfold thetaN thetaL
    rw [← (Equiv.funUnique (Fin 1) L).symm.tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.funUnique_symm_apply, Fin.sum_univ_one]
    congr 1
    simp [uniqueElim_const]
    ring

end Formalism.HermitianLatticesTheory
end
end

