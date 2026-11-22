import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.AsmBound
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LatticeFinitelyGenerated

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.AsmDual
section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

def Adapted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∃ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) ∧
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e ∧
      Submodule.span K (Set.range u) = U ∧
      (∀ i, Fin.append u z i ∈ cutE A e A.L) ∧
      LinearIndependent K y ∧ (∀ i, y i ∈ lamSub A e h U) ∧
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) ∧
      (cutE A e A.L).FG ∧ (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K (cutE A e A.L : Set A.V) = Submodule.span K (Set.range (Fin.append u z)) ∧
      Submodule.span K ((cutE A e A.L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) A.V) : Set A.V) =
        Submodule.span K (Set.range u)

lemma linInd_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] {k d : ℕ} (u : Fin k → V)
    (z : Fin d → V) (h : LinearIndependent K (Fin.append u z)) : LinearIndependent K u := by
  have : u = Fin.append u z ∘ Fin.castAdd d := by funext i; simp
  rw [this]
  exact h.comp _ (Fin.castAdd_injective k d)

theorem degDual_of (hFG : LamFG) (hAd : Adapted) (hAI : ArchIdentity) (hLP : LocalPairing)
    (hCP : ConjPrime) (hNF : NormFinsum) : DegDual := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  obtain ⟨k, d, u, z, y, hlin, hspz, hspu, hzM, hy, hyM, hspy, hMfg, hSfg, hspM, hspS⟩ :=
    hAd K A e n h hyp U hU
  have hfg := hFG K A e n h hyp U hU
  have hu : LinearIndependent K u := linInd_left u z hlin
  set M := cutE A e A.L with hM
  set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hS'
  set Λ := lamSub A e h U with hΛ
  rw [degL_eq_neg_lcv A hP.1 S hSfg u hu hspS, degL_eq_neg_lcv A hP.1 M hMfg _ hlin hspM,
    degL_eq_neg_lcv A hP.1 Λ hfg y hy hspy]
  have hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0 := fun i => (hyM i).2.1
  have hye : ∀ i, y i ∈ LinearMap.range e := fun i => (hyM i).1
  have harch := hAI K A e n h hyp U hU k d u z y hlin hspz hspu hy hye hyU
  obtain ⟨c, hcinv, hc⟩ := hCP K
  have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
  set D := (Matrix.of fun i j => h (y i) (z j)).det with hD
  set zf := Fin.append u z with hzf
  set Ly := Submodule.span (𝓞 K) (Set.range y)
  set Lz := Submodule.span (𝓞 K) (Set.range zf)
  set Lu := Submodule.span (𝓞 K) (Set.range u)
  have hloc : ∀ w, (vAdd w D : ℝ) + (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal Ly Λ : ℝ) +
      (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ) = 0 := by
    intro w
    have := hLP K A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyM hspy w (c w) (hc w).1
    exact_mod_cast this

  have fV := vAdd_support_finite (K := K) D
  have fY := lidx_support_finite A hP.1 Λ hfg y hy hspy
  have fZ := lidx_support_finite A hP.1 M hMfg zf hlin hspM
  have fU := lidx_support_finite A hP.1 S hSfg u hu hspS
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (vAdd w D : ℝ)
  set gy : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Ly Λ : ℝ)
  set gz : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ)
  set gu : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ)
  have sub : ∀ {x : HeightOneSpectrum (𝓞 K) → ℤ}, (Function.support x).Finite →
      (Function.support fun w => lw K w * (x w : ℝ)).Finite := fun hx =>
    hx.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have fa : (Function.support a).Finite := sub fV
  have fgy : (Function.support gy).Finite := sub fY
  have fgz : (Function.support gz).Finite := sub fZ
  have fgu : (Function.support gu).Finite := sub fU
  have fgyc : (Function.support fun w => gy (c w)).Finite :=
    (fgy.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsum0 : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = 0 := by
    have : (fun w => a w + gy (c w) + gz w - gu w) = fun _ => (0 : ℝ) := by
      funext w
      simp only [a, gy, gz, gu]
      rw [hlwc w]
      have := hloc w
      linear_combination lw K w * this
    rw [this, finsum_zero]
  have hsym : (∑ᶠ w, gy (c w)) = ∑ᶠ w, gy w := by
    have : (fun w => gy (c w)) = fun w => gy (Function.Involutive.toPerm c hcinv w) := by
      funext w; simp
    rw [this]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) =
      (∑ᶠ w, a w) + (∑ᶠ w, gy (c w)) + (∑ᶠ w, gz w) - ∑ᶠ w, gu w := by
    rw [finsum_sub_distrib ((fa.union fgyc).union fgz |>.subset ?_) fgu,
      finsum_add_distrib ((fa.union fgyc).subset (Function.support_add _ _)) fgz,
      finsum_add_distrib fa fgyc]
    intro w hw
    simp only [Function.mem_support] at hw
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hw
    rw [hn.1.1, hn.1.2, hn.2]; ring
  rw [hsplit, hsym] at hsum0

  have hnorm : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ) = ∑ᶠ w, a w := by
    by_cases hD0 : D = 0
    · simp only [a]
      rw [hD0]
      simp [vAdd]
    · exact (hNF K D hD0).symm
  unfold lcv lcvInf
  rw [lcvFin_eq A u, lcvFin_eq A zf, lcvFin_eq A y]
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk] at hnorm
  have e1 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re -
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re =
      2 * (∑ᶠ w, a w) - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [← hnorm, ← harch]
    field_simp
    ring
  change -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re + 2 * ∑ᶠ w, gu w) -
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re + 2 * ∑ᶠ w, gz w) =
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re + 2 * ∑ᶠ w, gy w)
  linarith

theorem partB_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PartB :=
  partB_of (degDual_of hFG hAd hAI hLP hCP hNF) (degDualBound_of hFG hCS hLG hCP hNF)

theorem dvProjRows_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PI.Dv.division_rows_base_level :=
  dvProjRows_of (partB_of_pieces hFG hAd hCS hAI hLG hLP hCP hNF)

end PI.DvRows
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LocFree
section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain

def LocFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (Y : Submodule (𝓞 K) V), Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      Submodule.span K (Set.range b) = Submodule.span K (Y : Set V) ∧ (∀ i, b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ Submodule.span (𝓞 K) (Set.range b)

section Den

variable {K : Type} [Field K] [NumberField K]

lemma den_of_locP {V : Type*} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {X Y : Submodule (𝓞 K) V} (hY : Y.FG) (hYX : Y ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X) :
    ∃ T : 𝓞 K, T ∉ w.asIdeal ∧ ∀ y ∈ Y, T • y ∈ X := by
  classical
  obtain ⟨S, rfl⟩ := hY
  have hs : ∀ g : S, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (g : V) ∈ X := fun g => by
    obtain ⟨s, hs, hx⟩ := (mem_locP' w.asIdeal).1 (hYX (Submodule.subset_span g.2))
    exact ⟨s, hs, hx⟩
  choose s hsw hsX using hs
  have hT : (∏ g, s g) ∈ w.asIdeal.primeCompl := Submonoid.prod_mem _ fun g _ => hsw g
  refine ⟨∏ g, s g, hT, ?_⟩
  have key : Submodule.span (𝓞 K) (S : Set V) ≤
      X.comap ((∏ g, s g) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    have hx' : x ∈ S := Finset.mem_coe.1 hx
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact X.smul_mem _ (hsX ⟨x, hx'⟩)
  intro y hy
  exact key hy

end Den

theorem lattice_locally_free : LocFree := by
  intro K _ _ V _ _ _ _ w Y hY
  let _ : StarRing K := starRingOfComm
  obtain ⟨T, hT⟩ := hY
  obtain ⟨B, hBT, hBsp, hBli⟩ := exists_linearIndependent K (T : Set V)
  have hBfin : B.Finite := (T.finite_toSet).subset hBT
  have := hBfin.fintype
  set r := Fintype.card B with hr
  set eB := Fintype.equivFin B with heB
  set v : Fin r → V := fun i => ((eB.symm i : B) : V) with hv
  have hvli : LinearIndependent K v := hBli.comp _ eB.symm.injective
  have hvY : ∀ i, v i ∈ Y := fun i => hT ▸ Submodule.subset_span (hBT (eB.symm i).2)
  have hrv : Set.range v = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eB.symm i).2
    · intro hx
      exact ⟨eB ⟨x, hx⟩, by simp [hv]⟩
  have hvsp : Submodule.span K (Set.range v) = Submodule.span K (Y : Set V) := by
    rw [hrv, hBsp, ← hT, Submodule.span_span_of_tower]
  set f : (Fin r → K) →ₗ[K] V := combo v with hf
  set fO : (Fin r → K) →ₗ[𝓞 K] V := f.restrictScalars (𝓞 K) with hfO
  have hfinj : Function.Injective f := by
    intro a b hab
    have h2 : combo v (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    rw [combo_apply] at h2
    have := (Fintype.linearIndependent_iff.1 hvli) _ h2
    funext i
    exact sub_eq_zero.1 (this i)
  have hfsingle : ∀ i, f (Pi.single i 1) = v i := by
    intro i
    rw [hf, combo_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  have hfmem : ∀ x, f x ∈ Submodule.span K (Set.range v) := by
    intro x
    rw [hf, combo_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : ∀ y ∈ Submodule.span K (Set.range v), ∃ x, f x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
    exact ⟨c, by rw [hf, combo_apply, hc]⟩
  set Y' : Submodule (𝓞 K) (Fin r → K) := Y.comap fO with hY'
  have hmapY : Y'.map fO = Y := by
    apply le_antisymm (Submodule.map_comap_le _ _)
    intro y hy
    obtain ⟨x, hx⟩ := hrange y (by rw [hvsp]; exact Submodule.subset_span hy)
    refine ⟨x, ?_, hx⟩
    show f x ∈ Y
    rw [hx]; exact hy
  have hY'fg : Y'.FG := Submodule.fg_of_fg_map_injective fO hfinj (by rw [hmapY]; exact ⟨T, hT⟩)
  have hstd : ∀ i, (Pi.single i 1 : Fin r → K) ∈ Y' := by
    intro i
    rw [hY', Submodule.mem_comap]
    show f (Pi.single i 1) ∈ Y
    rw [hfsingle]; exact hvY i
  have hY'sp : Submodule.span K (Y' : Set (Fin r → K)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hstd i)
  have hlat : Submodule.IsLattice K Y' := ⟨hY'fg, hY'sp⟩
  obtain ⟨g, hgli, hgloc⟩ := Formalism.DivisionValues.semilocal_basis_exists K r Y' hlat w
  have hgtop : Submodule.span K (Set.range g) = ⊤ := Formalism.DivisionValues.idxChange_span_top hgli

  set b0 : Fin r → V := fun i => f (g i) with hb0
  have hb0li : LinearIndependent K b0 := hgli.map' f (LinearMap.ker_eq_bot.2 hfinj)
  have hb0sp : Submodule.span K (Set.range b0) = Submodule.span K (Y : Set V) := by
    rw [← hvsp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hfmem (g i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : (Pi.single i 1 : Fin r → K) ∈ Submodule.span K (Set.range g) := by
        rw [hgtop]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := f) h1
      rw [Submodule.map_span, ← Set.range_comp, hfsingle] at h2
      exact h2
  have hloc1 : ∀ x ∈ Submodule.span (𝓞 K) (Set.range g),
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y' := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal Y' := by
      rw [← hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩
  have hloc2 : ∀ x ∈ Y', ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      s • x ∈ Submodule.span (𝓞 K) (Set.range g) := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range g)) := by
      rw [hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩

  have hb0loc : Submodule.span (𝓞 K) (Set.range b0) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal Y := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hloc1 (g i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨s, hs, ?_⟩
    have : fO (s • g i) ∈ Y := hsx
    rwa [map_smul] at this
  obtain ⟨t, htw, htY⟩ := den_of_locP w (Submodule.fg_span (Set.finite_range b0)) hb0loc
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    intro h0; apply htw
    have : t = 0 := by simpa using h0
    rw [this]; exact w.asIdeal.zero_mem
  have e : (fun i => t • b0 i) = fun i => (algebraMap (𝓞 K) K t) • b0 i := by
    funext i; rw [algebraMap_smul]
  refine ⟨r, fun i => t • b0 i, ?_, ?_, ?_, ?_⟩
  · rw [e, Fintype.linearIndependent_iff]
    intro gg hgg i
    have h3 : ∑ i, (gg i * algebraMap (𝓞 K) K t) • b0 i = 0 := by
      rw [← hgg]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]
    have := (Fintype.linearIndependent_iff.1 hb0li) _ h3 i
    exact (mul_eq_zero.1 this).resolve_right ht0
  · rw [e, ← hb0sp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h4 : b0 i = (algebraMap (𝓞 K) K t)⁻¹ • ((algebraMap (𝓞 K) K t) • b0 i) := by
        rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [SetLike.mem_coe, h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    exact htY _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro y hy
    obtain ⟨x, hxY, rfl⟩ := (by rw [hmapY]; exact hy : y ∈ Y'.map fO)
    obtain ⟨s, hs, hsx⟩ := hloc2 x hxY
    refine ⟨t * s, ?_, ?_⟩
    · intro hm
      rcases w.isPrime.mem_or_mem hm with h | h
      · exact htw h
      · exact hs h
    · have h1 : fO (s • x) ∈ (Submodule.span (𝓞 K) (Set.range g)).map fO :=
        Submodule.mem_map_of_mem hsx
      rw [Submodule.map_span, ← Set.range_comp] at h1
      rw [map_smul] at h1
      rw [mul_smul]
      have h2 : Submodule.span (𝓞 K) (Set.range (fO ∘ g)) ≤
          (Submodule.span (𝓞 K) (Set.range fun i => t • b0 i)).comap (t • LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact h2 h1

end PI.DvRows
end
end

