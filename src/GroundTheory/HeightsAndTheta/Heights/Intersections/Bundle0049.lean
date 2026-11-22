import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrderOne

section Length

variable {A : Type*} [CommRing A]

theorem length_eq_one_of_sat (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by
  have hz : ∀ (r : A) (s : W.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk J r) s = 0 ↔ r ∈ W := by
    intro r s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨u, hu⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
      rcases ‹W.IsPrime›.mem_or_mem (hJ hu) with h | h
      · exact absurd h u.2
      rcases ‹W.IsPrime›.mem_or_mem h with h | h
      · exact absurd h s.2
      · exact h
    · intro hr
      obtain ⟨u, hu, hud⟩ := hs r hr
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : u * ((s : A) * r) = u * r * s := by ring
      rw [show ((⟨u, hu⟩ : W.primeCompl) : A) = u from rfl, e]
      exact J.mul_mem_right _ hud
  have hgen : ∀ (q : A) (t : W.primeCompl) (r : A) (s : W.primeCompl) (hr : r ∉ W),
      LocalizedModule.mk (Ideal.Quotient.mk J q) t =
        Localization.mk (q * s) (t * ⟨r, hr⟩) • LocalizedModule.mk (Ideal.Quotient.mk J r) s := by
    intro q t r s hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul]
    congr 1
    ring
  have h1 : LocalizedModule.mk (Ideal.Quotient.mk J 1) (1 : W.primeCompl) ≠ 0 :=
    fun h => ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).2 ((hz 1 1).1 h))
  have : Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨⟨_, 0, h1⟩⟩
  rw [Module.length_eq_one_iff, isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).1 hN
  induction n using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hr : r ∉ W := fun h => hn0 ((hz r s).2 h)
    rw [eq_top_iff]
    intro y _
    induction y using LocalizedModule.induction_on with
    | h m' t =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [hgen q t r s hr]
      exact N.smul_mem _ hnN

end Length

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem isWeightedHomogeneous_multiConeMap (c : (Σ k, ι k) → Φ) {p : MRing ι} {m : K → ℕ}
    (hp : IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) p m) :
    IsWeightedHomogeneous (fun k : K => (Pi.single k 1 : K → ℕ)) (T.multiConeMap c p) m := by
  rw [DiagRAux.multiConeMap_of_homog c p m ((isMultiHomog_iff_weighted p m).2 hp)]
  have := (isWeightedHomogeneous_C (fun k : K => (Pi.single k 1 : K → ℕ)) (aeval c p)).mul
    (IsWeightedHomogeneous.prod Finset.univ (fun k => (X k : MvPolynomial K Φ) ^ m k)
      (fun k => m k • (Pi.single k 1 : K → ℕ)) (fun k _ => (isWeightedHomogeneous_X Φ _ k).pow (m k)))
  convert this using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem component_mem_ker (c : (Σ k, ι k) → Φ) {f : MRing ι} (hf : f ∈ RingHom.ker (T.multiConeMap c))
    (m : K → ℕ) :
    weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f ∈
      RingHom.ker (T.multiConeMap c) := by
  rw [RingHom.mem_ker] at hf ⊢
  have hsum := congrArg (weightedHomogeneousComponent (fun k : K => (Pi.single k 1 : K → ℕ)) m) hf
  rw [← sum_weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum, map_zero] at hsum
  rw [← (isWeightedHomogeneous_multiConeMap c
    (weightedHomogeneousComponent_isWeightedHomogeneous m f)).weightedHomogeneousComponent_same, ← hsum]
  by_cases hm : weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f = 0
  · rw [hm, map_zero, map_zero]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = m
    · rw [hb, hm, map_zero, map_zero]
    · exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
  · rw [Finset.sum_eq_single m]
    · intro b _ hb
      exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset _).2 hm) h

end Graded

end DiagonalOrderOne

open DiagonalOrderOne in

theorem DiagOrdOne.proof (hF : DiagFormDiv.Statement) : DiagOrdOne.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  set P := T.wwIdeal x δ e φ (a 0) (a 1) with hPdef
  set Δ := T.wwIdeal x δ e φ (a 0) (a 0) with hΔdef
  have hΔp : Δ.IsPrime := RingHom.ker_isPrime _
  have hPΔ : P ≤ Δ := DiagonalOrder.wwIdeal_le_diag x δ e φ a ha
  have hhΔ : h ∉ Δ := by
    refine (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).2 ?_
    rw [DiagonalOrder.aeval_diag_eq x δ e φ (a 0) (a 1) hh]
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
  have hJ : P ⊔ Ideal.span {g} ≤ Δ := sup_le hPΔ
    ((Ideal.span_singleton_le_iff_mem _).2 (DiagFormDiv.mem_diag_of_quot x δ e φ a ha hg hh hq))
  have hhom : ∀ (α : T.WBlk → ℕ) (d : MRing (T.wwIdx ι ν κ)), IsMultiHomog d α → d ∈ Δ →
      ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g} := by
    intro α d hd hdΔ
    obtain ⟨γ, β, s, r, hs, hr, hdeg, hsΔ, hv⟩ := hF Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha α d hd hdΔ
    refine ⟨s * h, fun hm => (hΔp.mem_or_mem hm).elim hsΔ hhΔ, ?_⟩
    have hdeg' : β + T.wwDeg n 1 = γ + T.wwDeg (n + 3) 0 + α := by
      funext k
      have := hdeg k
      cases k <;> simp only [T.wwDeg, Pi.add_apply] at this ⊢ <;> omega
    have hm : IsMultiHomog (s * h * d - r * g) (γ + T.wwDeg (n + 3) 0 + α) :=
      exHomog_sub (exHomog_mul (exHomog_mul hs hh) hd) (hdeg' ▸ exHomog_mul hr hg)
    have hmP : s * h * d - r * g ∈ P := by
      by_contra hn
      apply (DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hm).1 hn
      rw [map_sub, map_mul, map_mul, map_mul, hq]
      linear_combination (aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) * hv
    have e' : s * h * d = (s * h * d - r * g) + r * g := by ring
    rw [e']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hmP)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  have hsat : ∀ d ∈ Δ, ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g} := by
    intro d hd
    rw [← sum_weightedHomogeneousComponent (fun q : Σ k, T.wwIdx ι ν κ k => (Pi.single q.1 1 : T.WBlk → ℕ)) d,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp d)]
    refine Finset.sum_induction _ (fun y => ∃ u ∉ Δ, u * y ∈ P ⊔ Ideal.span {g}) ?_ ⟨1, ?_, by simp⟩ ?_
    · rintro y z ⟨u, hu, huy⟩ ⟨v, hv, hvz⟩
      refine ⟨u * v, fun hm => (hΔp.mem_or_mem hm).elim hu hv, ?_⟩
      have e' : u * v * (y + z) = v * (u * y) + u * (v * z) := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ huy) (Ideal.mul_mem_left _ _ hvz)
    · exact fun h1 => hΔp.ne_top ((Ideal.eq_top_iff_one Δ).2 h1)
    · intro m _
      exact hhom m _ ((isMultiHomog_iff_weighted _ m).2 (weightedHomogeneousComponent_isWeightedHomogeneous m d))
        (component_mem_ker _ hd m)
  unfold multAt
  rw [dif_pos hΔp, length_eq_one_of_sat _ Δ hJ hsat]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingInj.le_of_locRing_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by
  classical
  have := hP
  have hL := LocRingLocal.proof LocRingFrac.proof
  set φ := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) with hφ
  have hne : ∀ {f : MRing ι}, f ∉ P → φ (Ideal.Quotient.mk P f) ≠ 0 := fun hf h => hf <| by
    rwa [hφ, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h

  have hunit : ∀ {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) (hy' : y ∈ locRing P W'),
      IsUnit (⟨y, hy'⟩ : locRing P W') → IsUnit (⟨y, hy⟩ : locRing P W) := by
    intro y hy hy' hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hb' : y * (b : FractionRing (MRing ι ⧸ P)) = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] at this
    have hbW : (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by rw [heq]; exact b.2
    refine IsUnit.of_mul_eq_one (⟨b, hbW⟩ : locRing P W) (Subtype.ext ?_)
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk, hb']
  choose i hi using hW.2.2
  choose j hj using hW'.2.2

  have hjW : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ W := by
    intro k
    have hiP : (X ⟨k, i k⟩ : MRing ι) ∉ P := fun h => hi k (hPW h)
    have hjP : (X ⟨k, j k⟩ : MRing ι) ∉ P := fun h => hj k (hPW' h)
    have h1 : φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) ∈ locRing P W :=
      heq ▸ frac_mem_locRing hPW' (AvoidRing.isMultiHomog_X k (i k)) (AvoidRing.isMultiHomog_X k (j k))
        (hj k) (div_mul_cancel₀ _ (hne hjP))
    have h2 : φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) ∈ locRing P W :=
      frac_mem_locRing hPW (AvoidRing.isMultiHomog_X k (j k)) (AvoidRing.isMultiHomog_X k (i k))
        (hi k) (div_mul_cancel₀ _ (hne hiP))
    have hu : IsUnit (⟨_, h2⟩ : locRing P W) := by
      refine IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing P W) (Subtype.ext ?_)
      rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk]
      have := hne hiP
      have := hne hjP
      field_simp
    exact ((hL K ι P W hP hW.1 hPW).2 _ _ _ _ (AvoidRing.isMultiHomog_X k (j k))
      (AvoidRing.isMultiHomog_X k (i k)) (hi k) (div_mul_cancel₀ _ (hne hiP))).mp hu

  obtain ⟨S, hS, hWS⟩ := hW.2.1
  rw [hWS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
  by_contra hfW'
  have htW := AvoidRing.coordProd_not_mem hW.1 j hjW a
  have htW' := AvoidRing.coordProd_not_mem hW'.1 j hj a
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι) j a
  have hy := div_mul_cancel₀ (φ (Ideal.Quotient.mk P f)) (hne fun h => htW (hPW h))
  have hyW := frac_mem_locRing hPW ha ht htW hy
  have hyW' := frac_mem_locRing hPW' ha ht htW' hy
  have hu' : IsUnit (⟨_, hyW'⟩ : locRing P W') :=
    ((hL K ι P W' hP hW'.1 hPW').2 _ f _ a ha ht htW' hy).mpr hfW'
  exact ((hL K ι P W hP hW.1 hPW).2 _ f _ a ha ht htW hy).mp (hunit hyW hyW' hu') hfW

theorem LocRingInj.proof : LocRingInj.Statement := by
  intro K _ ι _ P W W' hP hW hW' hPW hPW' heq
  exact le_antisymm (LocRingInj.le_of_locRing_eq hP hW hW' hPW hPW' heq)
    (LocRingInj.le_of_locRing_eq hP hW' hW hPW' hPW heq.symm)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Loc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

theorem baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRing ι) :
    baseSubst κ G (rename v g) = C (aeval G.x g) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dif_pos h1, dif_pos h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h g

theorem baseSubst_X_fibre (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dif_neg q.1.2]

theorem mem_of_baseSubst_eq_zero (hv : IsBlockMap κ v) (G : GenFibre v P') {f : MRing ι'}
    (hf : baseSubst κ G f = 0) : f ∈ P' := by
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, hf, map_zero]

theorem baseSubst_mem_fibreIdeal (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    baseSubst κ G f ∈ fibreIdeal κ G ↔ f ∈ P' := by
  rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]

theorem exists_mul_eq_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (c : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (F : MRing ι') (g : MRing ι), aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G F := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, g, hg, rfl⟩ := G.gen a
    refine ⟨rename v f, g, hg, ?_⟩
    rw [baseSubst_rename hv, ← C_mul, div_mul_cancel₀ _ hg]
  | add c₁ c₂ ih₁ ih₂ =>
    obtain ⟨F₁, g₁, h₁, e₁⟩ := ih₁
    obtain ⟨F₂, g₂, h₂, e₂⟩ := ih₂
    refine ⟨F₁ * rename v g₂ + F₂ * rename v g₁, g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hv]
    rw [← e₁, ← e₂]
    ring
  | mul_X c q ih =>
    obtain ⟨F, g, hg, e⟩ := ih
    refine ⟨F * X ⟨q.1.1, q.2⟩, g, hg, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fibre]
    ring

theorem mem_fibreOf_of_mul_eq (G : GenFibre v P') {I : Ideal (MRing ι')} {c : MRingOver G.Φ (fibreIdx ι' κ)}
    {F : MRing ι'} {g : MRing ι} (hg : aeval G.x g ≠ 0) (e : c * C (aeval G.x g) = baseSubst κ G F) (hF : F ∈ I) :
    c ∈ fibreOf κ G I := by
  have : c = baseSubst κ G F * C (aeval G.x g)⁻¹ := by
    rw [← e, mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hF)

theorem fibreOf_comap (hv : IsBlockMap κ v) (G : GenFibre v P') (Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))) :
    fibreOf κ G (Q.comap (baseSubst κ G)) = Q := by
  refine le_antisymm Ideal.map_comap_le fun c hc => ?_
  obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
  refine mem_fibreOf_of_mul_eq G hg e ?_
  rw [Ideal.mem_comap, ← e]
  exact Q.mul_mem_right _ hc

theorem comap_fibreOf (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).comap (baseSubst κ G) = W := by
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  have key : ∀ c ∈ fibreOf κ G W, ∃ w ∈ W, ∃ g : MRing ι, aeval G.x g ≠ 0 ∧
      c * C (aeval G.x g) = baseSubst κ G w := by
    intro c hc
    unfold fibreOf Ideal.map Ideal.span at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨w, hw, rfl⟩ := hc
      exact ⟨w, hw, 1, by simp, by simp⟩
    | zero => exact ⟨0, W.zero_mem, 1, by simp, by simp⟩
    | add c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁, g₁, h₁, e₁⟩ := ih₁
      obtain ⟨w₂, hw₂, g₂, h₂, e₂⟩ := ih₂
      refine ⟨w₁ * rename v g₂ + w₂ * rename v g₁, W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_right _ hw₂),
        g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
      simp only [map_add, map_mul, baseSubst_rename hv]
      rw [← e₁, ← e₂]
      ring
    | smul a c _ ih =>
      obtain ⟨w, hw, g, h, e⟩ := ih
      obtain ⟨F, g', h', e'⟩ := exists_mul_eq_baseSubst hv G a
      refine ⟨F * w, W.mul_mem_left _ hw, g' * g, by rw [map_mul]; exact mul_ne_zero h' h, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [← e', ← e]
      ring
  obtain ⟨w, hw, g, hg, e⟩ := key _ hf
  have h0 : f * rename v g - w ∈ P' :=
    mem_of_baseSubst_eq_zero hv G (by rw [map_sub, map_mul, baseSubst_rename hv, e, sub_self])
  have h1 : f * rename v g ∈ W := by simpa using W.add_mem (hPW h0) hw
  rcases hW.mem_or_mem h1 with h | h
  · exact h
  · refine absurd ?_ hg
    have hg' : g ∈ imageZ v W := h
    rw [hI, ← G.ker_x] at hg'
    exact hg'

theorem fibreOf_isPrime (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).IsPrime := by
  have hc := comap_fibreOf hv G hW hPW hI
  refine ⟨fun h => hW.ne_top ?_, fun {a b} hab => ?_⟩
  · rw [← hc, h, Ideal.comap_top]
  · obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G a
    obtain ⟨H, g', hg', e'⟩ := exists_mul_eq_baseSubst hv G b
    have hFH : F * H ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e, ← e']
      have : a * C (aeval G.x g) * (b * C (aeval G.x g')) = a * b * (C (aeval G.x g) * C (aeval G.x g')) := by
        ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hab
    rcases hW.mem_or_mem hFH with h | h
    · exact Or.inl (mem_fibreOf_of_mul_eq G hg e h)
    · exact Or.inr (mem_fibreOf_of_mul_eq G hg' e' h)

theorem imageZ_comap (hv : IsBlockMap κ v) (G : GenFibre v P') {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}
    (hQ : Q ≠ ⊤) : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := by
  ext g
  rw [← G.ker_x, RingHom.mem_ker, imageZ, Ideal.mem_comap, Ideal.mem_comap]
  show baseSubst κ G (rename v g) ∈ Q ↔ _
  rw [baseSubst_rename hv]
  constructor
  · intro h
    by_contra hne
    exact hQ (Q.eq_top_of_isUnit_mem h ((isUnit_iff_ne_zero.mpr hne).map C))
  · intro h
    rw [h, map_zero]
    exact Q.zero_mem

end Loc

theorem PFFibreBij.proof : PFFibreBij.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s hv hP' hP
  classical
  have hPrel : IsRelevant (imageZ v P') := hP.2.1.2.2
  have hPhor : IsHorizontal (imageZ v P') := hP.2.2.1
  have hfib : ∀ {W : Ideal (MRing ι')}, P' ≤ W → fibreIdeal κ G ≤ fibreOf κ G W := by
    intro W hW c hc
    obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
    refine mem_fibreOf_of_mul_eq G hg e (hW ?_)
    rw [← baseSubst_mem_fibreIdeal hv G, ← e]
    exact Ideal.mul_mem_right _ _ hc
  have hle : ∀ {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}, fibreIdeal κ G ≤ Q → P' ≤ Q.comap (baseSubst κ G) :=
    fun hQ f hf => hQ ((baseSubst_mem_fibreIdeal hv G f).mpr hf)
  refine ⟨?_, ?_, ?_⟩
  · rintro W ⟨⟨⟨⟨hWp, hWle⟩, hWmin⟩, hWrel⟩, -, hWI⟩
    have hPW := (sup_le_iff.mp hWle).1
    have hsW := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hWle).2
    have hcW := comap_fibreOf hv G hWp hPW hWI
    refine ⟨⟨⟨fibreOf_isPrime hv G hWp hPW hWI, sup_le (hfib hPW)
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW))⟩, ?_⟩, ?_⟩
    · rintro Q' ⟨hQ'p, hQ'le⟩ hQ'Q
      have hsQ' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQ'le).2
      have hm := hWmin ⟨Ideal.IsPrime.comap _ (hK := hQ'p), sup_le (hle (sup_le_iff.mp hQ'le).1)
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_comap.mpr hsQ'))⟩
        (by rw [← hcW]; exact Ideal.comap_mono hQ'Q)
      calc fibreOf κ G W ≤ fibreOf κ G (Q'.comap (baseSubst κ G)) := Ideal.map_mono hm
        _ = Q' := fibreOf_comap hv G Q'
    · intro k
      obtain ⟨i, hi⟩ := hWrel k.1
      refine ⟨i, fun h => hi ?_⟩
      rw [← hcW, Ideal.mem_comap, baseSubst_X_fibre G ⟨k, i⟩]
      exact h
  · rintro W₁ ⟨⟨⟨⟨h1p, h1le⟩, -⟩, -⟩, -, h1I⟩ W₂ ⟨⟨⟨⟨h2p, h2le⟩, -⟩, -⟩, -, h2I⟩ heq
    rw [← comap_fibreOf hv G h1p (sup_le_iff.mp h1le).1 h1I, heq,
      comap_fibreOf hv G h2p (sup_le_iff.mp h2le).1 h2I]
  · rintro Q ⟨⟨⟨hQp, hQle⟩, hQmin⟩, hQrel⟩
    have hWp : (Q.comap (baseSubst κ G)).IsPrime := Ideal.IsPrime.comap _ (hK := hQp)
    have hPW : P' ≤ Q.comap (baseSubst κ G) := hle (sup_le_iff.mp hQle).1
    have hsW : s ∈ Q.comap (baseSubst κ G) :=
      Ideal.mem_comap.mpr ((Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hQle).2)
    have hWI : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := imageZ_comap hv G hQp.ne_top
    have hmap : fibreOf κ G (Q.comap (baseSubst κ G)) = Q := fibreOf_comap hv G Q
    refine ⟨Q.comap (baseSubst κ G), ⟨⟨⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, ?_⟩, ?_⟩,
      ?_, hWI⟩, hmap⟩
    · rintro W' ⟨hW'p, hW'le⟩ hW'W
      have hPW' := (sup_le_iff.mp hW'le).1
      have hsW' := (Ideal.span_singleton_le_iff_mem _).mp (sup_le_iff.mp hW'le).2
      have hW'I : imageZ v W' = imageZ v P' :=
        le_antisymm (by rw [← hWI]; exact Ideal.comap_mono hW'W) (Ideal.comap_mono hPW')
      have hm := hQmin ⟨fibreOf_isPrime hv G hW'p hPW' hW'I, sup_le (hfib hPW')
        ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hsW'))⟩
        (by rw [← hmap]; exact Ideal.map_mono hW'W)
      calc Q.comap (baseSubst κ G) ≤ (fibreOf κ G W').comap (baseSubst κ G) := Ideal.comap_mono hm
        _ = W' := comap_fibreOf hv G hW'p hPW' hW'I
    · intro k'
      by_cases hk : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := hk
        obtain ⟨i, hi⟩ := hPrel k
        have hx : (X (v ⟨k, i⟩) : MRing ι') ∉ Q.comap (baseSubst κ G) := fun h => hi (by
          rw [← hWI, imageZ, Ideal.mem_comap]
          show rename v (X ⟨k, i⟩) ∈ Q.comap (baseSubst κ G)
          rw [rename_X]
          exact h)
        have hvk := hv.2.2.1 ⟨k, i⟩
        generalize v ⟨k, i⟩ = q at hx hvk
        obtain ⟨k'', j⟩ := q
        simp only at hvk
        subst hvk
        exact ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := hQrel ⟨k', hk⟩
        refine ⟨i, fun h => hi ?_⟩
        rw [← baseSubst_X_fibre G ⟨⟨k', hk⟩, i⟩]
        exact h
    · rw [IsHorizontal, eq_bot_iff]
      intro n hn
      have hn' : n ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, ← hWI, imageZ, Ideal.mem_comap]
        show rename v (C n) ∈ Q.comap (baseSubst κ G)
        rw [rename_C]
        exact Ideal.mem_comap.mp hn
      rw [hPhor] at hn'
      exact hn'

end

end GroundTheory.Heights₂.Heights.Inter
end

