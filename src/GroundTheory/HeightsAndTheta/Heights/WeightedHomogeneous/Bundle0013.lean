import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

theorem YPlusMetric.proof (hF : ChartFormsAlt.Statement) (hG : HomogGeneratorsExist.Statement)
    (hM : ChartMetric.Statement) (hP : ConePoints.Statement) : YPlusMetric.Statement := by
  intro ι _ _ n P D Ω _ y x' N hR hdeg hconj
  obtain ⟨d₀, hd₀⟩ := hF ι n P D
  obtain ⟨g, hg⟩ := hd₀ d₀ le_rfl
  obtain ⟨r, G, δ, hGen⟩ := hG ι n P
  obtain ⟨⟨H, hHdeg, hHmet, hHconj⟩, hval⟩ := hM ι n P D N hdeg d₀ g hg r G δ hGen
  refine ⟨H, hHdeg, hHconj hconj, ?_⟩
  intro j g' m dg dm hg' hm hdg hy z hz

  have hw : unflatCone z ∈ D.extPoints := by
    refine ⟨(blockNonzero_unflatCone_iff z).mpr hz.1, fun f hf ↦ ?_⟩
    rw [hR.ext_eq] at hf
    rw [← eval_map_flatCone, flatCone_unflatCone]
    exact hz.2 f hf
  obtain ⟨hold, la, _, hnew⟩ := (hP ι n P D d₀ g hg).2 _ hw
  have hev : ∀ f : MvPolynomial (Coord n) ℤ,
      evalCone (D.basePart₂ (unflatCone z)) f = eval (D.oldFlat z) (map (Int.castRingHom ℂ) f) := by
    intro f
    rw [← eval_map_flatCone]
    rfl

  have hex : ∀ k, ∃ i, D.basePart₂ (unflatCone z) k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hold.1 k)
  choose c hc using hex
  have hmc : evalCone (D.basePart₂ (unflatCone z)) (chartMonomial c d₀) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hlive : P.IsLive c := by
    intro k hk
    apply hc k
    have := hold.2 _ hk
    simpa [evalCone] using this

  have hdeg' : ∀ k, (dg k : ℤ) = dm k + D.deg k := fun k ↦ by
    rw [hdg k, ← hdeg]; rfl
  have h1 : P.mkF g' = D.elt j * P.mkF m :=
    ((hR.reads j) g' m dg dm ((geoMultiHomog_iff _ _).mp hg') ((geoMultiHomog_iff _ _).mp hm) hdeg').mp
      (by rw [hy, mul_comm])
  have hcross : chartMonomial c d₀ * g' - m * g c j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h1, hg.value c hlive j]
    ring
  have hcz := hold.2 _ hcross
  rw [hev] at hcz
  simp only [map_sub, map_mul, sub_eq_zero] at hcz

  have hblk : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff z).mpr hz.1
  have hoblk : BlockNonzero (unflatCone (D.oldFlat z)) := hold.1
  have hHz : H.toGeo.h z = ‖la‖ * N.metric (D.basePart₂ (unflatCone z)) := by
    rw [HermLine.toGeo_h_of_blockNonzero _ hblk, hHmet _ hblk]
    exact hval _ hw c la hmc (hnew c hmc)
  rw [HermLine.toGeo_h_of_blockNonzero _ hoblk, hHz]
  have hzj : z ⟨none, j⟩ = la * evalCone (D.basePart₂ (unflatCone z)) (g c j) /
      evalCone (D.basePart₂ (unflatCone z)) (chartMonomial c d₀) := hnew c hmc j
  simp only [hev] at hzj hmc
  have key : z ⟨none, j⟩ * eval (D.oldFlat z) (map (Int.castRingHom ℂ) m) =
      la * eval (D.oldFlat z) (map (Int.castRingHom ℂ) g') := by
    rw [hzj, div_mul_eq_mul_div, div_eq_iff hmc]
    linear_combination (-la) * hcz
  have hnorm := congrArg (‖·‖) key
  simp only [norm_mul] at hnorm
  change _ = _ * (_ * N.metric (unflatCone (D.oldFlat z)))
  rw [hnorm]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSec
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace YPlusSec

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

def newEmb : (Σ _ : Unit, Fin (D.size + 1)) → Coord D.extSizes := fun p ↦ ⟨none, p.2⟩

theorem newEmb_injective : Function.Injective (newEmb D) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  exact congrArg (Sigma.mk ()) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem mapDomain_newEmb_none (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (j : Fin (D.extSizes none + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨none, j⟩ = m ⟨(), j⟩ :=
  Finsupp.mapDomain_apply (newEmb_injective D) m ⟨(), j⟩

theorem mapDomain_newEmb_some (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (k : ι)
    (i : Fin (D.extSizes (some k) + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨some k, i⟩ = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨p, hp⟩
  have h1 := congrArg (fun w : Coord D.extSizes ↦ w.1) hp
  simp [newEmb] at h1

end YPlusSec

open YPlusSec in

theorem YPlusSec.proof : YPlusSec.Statement := by
  intro ι _ _ n P D Ω _ y x' τ
  classical
  unfold Geo.secM
  congr 2
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range g (newEmb D) (newEmb_injective D) (by
      intro v hv
      rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
      obtain ⟨m, hm, hv⟩ := hv
      obtain ⟨o, i⟩ := v
      cases o with
      | none => exact ⟨⟨(), i⟩, rfl⟩
      | some k =>
        exfalso
        have h := hg m hm (some k)
        rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
        exact (Finsupp.mem_support_iff.mp hv) (h i (Finset.mem_univ _)))
    refine ⟨q, ?_, ?_⟩
    · intro m hm u
      cases u
      have hm' : Finsupp.mapDomain (newEmb D) m ∈ (rename (newEmb D) q).support := by
        rw [support_rename_of_injective (newEmb_injective D)]
        exact Finset.mem_image_of_mem _ hm
      have h := hg _ hm' none
      simp only [mapDomain_newEmb_none, Pi.single_eq_same] at h
      exact h
    · rw [aeval_rename]
      rfl
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rename (newEmb D) q, ?_, ?_⟩
    · intro m hm k
      rw [support_rename_of_injective (newEmb_injective D), Finset.mem_image] at hm
      obtain ⟨m, hm, rfl⟩ := hm
      cases k with
      | none =>
        simp only [mapDomain_newEmb_none, Pi.single_eq_same]
        exact hq m hm ()
      | some k =>
        simp only [mapDomain_newEmb_some, Finset.sum_const_zero]
        rw [Pi.single_eq_of_ne (Option.some_ne_none k)]
    · rw [aeval_rename]
      rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSupSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace YPlusSupSmall

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem eval_map_int {σ R : Type*} [CommRing R] (w : σ → R) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom R) p) = aeval w p := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem evalCone_unflatCone {κ : Type} {m : κ → ℕ} {R : Type*} [CommRing R] (w : Coord m → R)
    (p : MvPolynomial (Coord m) ℤ) : evalCone (unflatCone w) p = aeval w p := by
  rw [← eval_map_flatCone, flatCone_unflatCone, eval_map_int]

theorem exps {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) {m : Coord D.extSizes →₀ ℕ}
    (hm : m ∈ f.support) : (∀ k i, m ⟨some k, i⟩ = 0) ∧ ∑ j, m ⟨none, j⟩ = τ := by
  refine ⟨fun k i ↦ ?_, ?_⟩
  · have h := hf m hm (some k)
    rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
    exact h i (Finset.mem_univ _)
  · have h := hf m hm none
    rwa [Pi.single_eq_same] at h

theorem scale {R : Type*} [CommRing R] {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) (u w : Coord D.extSizes → R)
    (α β : R) (huw : ∀ j : Fin (D.size + 1), α * u ⟨none, j⟩ = β * w ⟨none, j⟩) :
    α ^ τ * aeval u f = β ^ τ * aeval w f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨h0, hτ⟩ := exps D hf hm
  have key : ∀ (v : Coord D.extSizes → R) (γ : R),
      γ ^ τ * ∏ p, v p ^ m p = ∏ j, (γ * v ⟨none, j⟩) ^ m ⟨none, j⟩ := by
    intro v γ
    rw [Fintype.prod_sigma, Fintype.prod_option]
    simp only [h0, pow_zero, Finset.prod_const_one, mul_one]
    rw [← hτ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  rw [mul_left_comm (α ^ τ), mul_left_comm (β ^ τ), key u α, key w β]
  exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ congrArg (· ^ m ⟨none, j⟩) (huw j))

theorem subst_homog {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ))
    (G : Coord D.extSizes → MvPolynomial (Coord n) ℤ) (e : ι → ℕ)
    (hG : ∀ v, IsWeightedHomogeneous (coordDeg n) (G v) e) :
    IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) := by
  rw [aeval_def, eval₂_eq']
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun v ↦ G v ^ m v) (fun v ↦ m v • e)
    fun v _ ↦ (hG v).pow (m v)
  have hs : ∑ v, m v • e = τ • e := by
    obtain ⟨h0, hτ⟩ := exps D hf hm
    rw [← Finset.sum_smul, Fintype.sum_sigma, Fintype.sum_option]
    simp [h0, hτ]
  rw [hs] at hp
  have hC : IsWeightedHomogeneous (coordDeg n) (algebraMap ℤ (MvPolynomial (Coord n) ℤ) (coeff m f)) 0 := by
    rw [algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  simpa using hC.mul hp

def newSubst (g : Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) :
    Coord D.extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => g j
  | ⟨some _, _⟩ => 0

end YPlusSupSmall

open YPlusSupSmall in

theorem YPlusSupSmall.proof (hForms : ChartFormsAlt.Statement) (hPts : ConePoints.Statement) :
    YPlusSupSmall.Statement := by
  intro ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hInd _ hsmall f hf hfs z hz
  classical
  obtain ⟨d, hd⟩ := hForms ι n P D
  obtain ⟨g, hg⟩ := hd d le_rfl
  have hζ : D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) :=
    D.oldFlat_mem_mcPts y x' z hz

  have hw : unflatCone z ∈ D.extPoints := by
    refine ⟨(blockNonzero_unflatCone_iff z).mpr hz.1, fun p hp ↦ ?_⟩
    rw [evalCone_unflatCone, ← eval_map_int]
    exact hz.2 p (hR.ext_eq ▸ hp)
  obtain ⟨-, la, hla, hrel⟩ := (hPts ι n P D d g hg).2 _ hw

  obtain ⟨c, hc⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z ⟨some k, c k⟩ ≠ 0 :=
    ⟨fun k ↦ (hz.1 (some k)).choose, fun k ↦ (hz.1 (some k)).choose_spec⟩
  have hmz : aeval (D.oldFlat z) (chartMonomial (n := n) c d) ≠ 0 := by
    simp only [chartMonomial, map_prod, map_pow, aeval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hlive : P.IsLive c := by
    intro k hk
    have h := hζ.2 _ (by rw [← hR.ideal_eq]; exact hk)
    rw [eval_map_int, aeval_X] at h
    exact hc k h

  obtain ⟨e, he⟩ : ∃ e : ι → ℕ, ∀ k, (e k : ℤ) = d k + D.deg k :=
    ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)⟩
  have hgh : ∀ j, IsWeightedHomogeneous (coordDeg n) (g c j) e := by
    intro j
    obtain ⟨δ, hδ, hδe⟩ := hg.homog c j
    have : δ = e := funext fun k ↦ by have h1 := hδe k; have h2 := he k; omega
    rwa [← this]
  have hmh : IsWeightedHomogeneous (coordDeg n) (chartMonomial (n := n) c d) d :=
    isWeightedHomogeneous_chartMonomial c d

  have hval : ∀ j, aeval y (g c j) = x' j * aeval y (chartMonomial c d) := fun j ↦
    (hR.reads j (g c j) (chartMonomial c d) e d (hgh j) hmh fun k ↦ he k).mpr
      (by rw [hg.value c hlive j, mul_comm])

  have hrelj : ∀ j : Fin (D.size + 1), aeval (D.oldFlat z) (chartMonomial c d) * z ⟨none, j⟩ =
      la * aeval (D.oldFlat z) (g c j) := by
    intro j
    have hold : D.basePart₂ (unflatCone z) = unflatCone (D.oldFlat z) := rfl
    have h := hrel c (by rw [hold, evalCone_unflatCone]; exact hmz) j
    rw [hold, evalCone_unflatCone, evalCone_unflatCone] at h
    change z ⟨none, j⟩ = _ at h
    rw [h]
    field_simp

  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (D.size + 1), z ⟨none, j⟩ ≠ 0 := hz.1 none
  have hAp : Ap.h z = ‖la‖ * N.h (D.oldFlat z) := by
    have h := hInd j₀ (g c j₀) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mpr (hgh j₀))
      ((geoMultiHomog_iff _ _).mpr hmh) (fun k ↦ by rw [hNa]; exact he k)
      (by rw [hval, mul_comm]) z hz
    rw [eval_map_int, eval_map_int] at h
    have hgz : aeval (D.oldFlat z) (g c j₀) ≠ 0 := by
      intro h0
      have h1 := hrelj j₀
      rw [h0, mul_zero] at h1
      exact mul_ne_zero hmz hj₀ h1
    have h2 := congrArg norm (hrelj j₀)
    rw [norm_mul, norm_mul] at h2
    apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hgz)
    linear_combination -h + N.h (D.oldFlat z) * h2

  set G := newSubst D (g c) with hG
  have hcomp : ∀ {R : Type} [CommRing R] (w : Coord n → R) (p : MvPolynomial (Coord D.extSizes) ℤ),
      aeval w (aeval G p) = aeval (fun v ↦ aeval w (G v)) p := fun w p ↦ by
    rw [← AlgHom.comp_apply, comp_aeval]
  have hFh : IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) :=
    subst_homog D hf G e (by rintro ⟨_ | k, i⟩; exacts [hgh i, isWeightedHomogeneous_zero _ _ _])
  have hFy : aeval y (aeval G f) = s * aeval y (chartMonomial c d ^ τ) := by
    have h := scale D hf (fun v ↦ aeval y (G v)) (D.plusCoord y x') 1 (aeval y (chartMonomial c d))
      (fun j ↦ by
        change 1 * aeval y (g c j) = aeval y (chartMonomial c d) * x' j
        rw [one_mul, hval, mul_comm])
    rw [one_pow, one_mul, hfs] at h
    rw [hcomp, h, map_pow, mul_comm]
  have hb := hsmall (τ • e) (τ • d) (aeval G f) (chartMonomial c d ^ τ) (D.oldFlat z)
    ((geoMultiHomog_iff _ _).mpr hFh) ((geoMultiHomog_iff _ _).mpr (hmh.pow τ))
    (fun k ↦ by simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k, hNa]; ring) hFy hζ
  rw [eval_map_int, eval_map_int, map_pow, norm_pow] at hb

  have hsc := scale D hf z (fun v ↦ aeval (D.oldFlat z) (G v)) (aeval (D.oldFlat z) (chartMonomial c d)) la
    (fun j ↦ hrelj j)
  rw [← hcomp] at hsc
  suffices hfin : ‖aeval z f‖ ≤ Ap.h z ^ τ from (congrArg norm (eval_map_int z f)).trans_le hfin
  have hpos : 0 < ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ := pow_pos (norm_pos_iff.mpr hmz) τ
  refine le_of_mul_le_mul_left ?_ hpos
  calc ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * ‖aeval z f‖
      = ‖la‖ ^ τ * ‖aeval (D.oldFlat z) (aeval G f)‖ := by
        rw [← norm_pow, ← norm_pow, ← norm_mul, ← norm_mul, hsc]
    _ ≤ ‖la‖ ^ τ * (‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * N.h (D.oldFlat z) ^ τ) := by
        gcongr
    _ = ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * Ap.h z ^ τ := by
        rw [hAp, mul_pow]; ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsPointHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def latticeValue {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (v : Fin m → K') (b : Fin (N + 1)) : K' :=
  ∑ j, algebraMap K K' (φ b j) * v j

def latticeExtend {K : Type*} [Field K] [NumberField K] (K' : Type*) [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun w : Fin m → K ↦ fun j ↦ algebraMap K K' (w j)) '' L)

def multiplierIdeal {L : Type*} [Field L] [NumberField L] {ι : Type*} (y : ι → L) :
    Submodule (𝓞 L) L where
  carrier := {a | ∀ i, a * y i ∈ Set.range (algebraMap (𝓞 L) L)}
  add_mem' := by
    intro a a' ha ha' i
    obtain ⟨c, hc⟩ := ha i
    obtain ⟨c', hc'⟩ := ha' i
    exact ⟨c + c', by rw [map_add, hc, hc', add_mul]⟩
  zero_mem' := fun _ ↦ ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨d, hd⟩ := ha i
    exact ⟨c * d, by rw [map_mul, hd, Algebra.smul_def, mul_assoc]⟩

def LatticeLineExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∃ A : HermLine (fun _ : Unit ↦ N), A.deg = 1 ∧ LatticeMetricAgrees φ F A ∧ A.ConjInvariant

def LineIdealDual.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin (r + 1) → K') (a : K'),
      a • v ∈ latticeExtend K' F.lattice ↔
        ∀ b, a * latticeValue φ v b ∈ Set.range (algebraMap (𝓞 K') K')

def IdealIndexPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : Type) [Fintype ι] (y : ι → L), y ≠ 0 →
    genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup *
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) = 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VarsSubsetRangeBlockIncl
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  subst h; rfl

omit [Fintype ι] [DecidableEq ι] in

theorem evalCone_rename_blockIncl {F : Type*} [CommRing F] (k₀ : ι) (z : Cone n F)
    (f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ) :
    evalCone z (rename (blockIncl k₀) f') = evalCone (projBlock k₀ z) f' := by
  unfold evalCone
  rw [eval₂_rename]
  rfl

omit [Fintype ι] in

theorem vars_subset_range_blockIncl (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    (f.vars : Set (Coord n)) ⊆ Set.range (blockIncl k₀) := by
  classical
  intro v hv
  obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support v).mp hv
  have hle : coordDeg n v ≤ Finsupp.weight (coordDeg n) d :=
    Finsupp.le_weight_of_ne_zero' (coordDeg n) (Finsupp.mem_support_iff.mp hdv)
  rw [hf (mem_support_iff.mp hd)] at hle
  have h1 := hle v.1
  obtain ⟨k, i⟩ := v
  by_cases hk : k = k₀
  · subst hk
    exact ⟨⟨(), i⟩, rfl⟩
  · simp [coordDeg, hk] at h1

omit [Fintype ι] in

theorem exists_blockForm (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (blockIncl k₀) f' = f := by
  classical
  obtain ⟨f', rfl⟩ := exists_rename_eq_of_vars_subset_range f (blockIncl k₀)
    (blockIncl_injective k₀) (vars_subset_range_blockIncl k₀ m f hf)
  refine ⟨f', fun d hd ↦ ?_, rfl⟩
  have hmem : Finsupp.mapDomain (blockIncl k₀) d ∈ (rename (blockIncl k₀) f').support := by
    rw [support_rename_of_injective (blockIncl_injective k₀)]
    exact Finset.mem_image_of_mem _ (mem_support_iff.mpr hd)
  have hw := hf (mem_support_iff.mp hmem)
  have hw' : Finsupp.weight (coordDeg n) (Finsupp.mapDomain (blockIncl k₀) d) =
      Finsupp.degree d • Pi.single k₀ 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) ↦ c • coordDeg n i)
      (fun _ ↦ zero_smul ℕ _) (fun _ _ _ ↦ add_smul _ _ _)]
    simp only [Finsupp.sum, coordDeg, blockIncl]
    rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl, Finset.sum_smul]
  rw [hw'] at hw
  have hdeg : Finsupp.degree d = m := by
    simpa using congrFun hw k₀
  funext u
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum, coordDeg, Finsupp.degree] at hdeg ⊢
  exact hdeg

theorem SupNormEquality.proof (hOnto : BlockSurjectivity.Statement) : SupNormEquality.Statement := by
  intro ι _ _ n P k₀ m
  refine ⟨fun f hf ↦ exists_blockForm k₀ m f hf, fun f' _ B ↦ ⟨fun h z' hz' ↦ ?_, fun h z hz ↦ ?_⟩⟩
  · rw [← hOnto ι n P k₀] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    simpa [evalCone_rename_blockIncl, projBlock] using h z hz
  · have hz' : projBlock k₀ z ∈ conePoints (P.projIdeal k₀) ℂ := by
      rw [← hOnto ι n P k₀]; exact ⟨z, hz, rfl⟩
    simpa [evalCone_rename_blockIncl, projBlock] using h _ hz'

end

end GroundTheory.Heights₂.Heights
end

