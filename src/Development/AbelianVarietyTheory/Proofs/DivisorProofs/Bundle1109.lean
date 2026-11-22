import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

def CxPts.conjEquiv {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E) (τ : E →+* ℂ) :
    CxPts q τ ≃ CxPts q (ComplexEmbedding.conjugate τ) :=
  (Points.conjHomeomorph S).toEquiv.subtypeEquiv fun y => by
    have e : spMap (ComplexEmbedding.conjugate τ) = spMap (starRingEnd ℂ) ≫ spMap τ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have : IsIso (spMap (starRingEnd ℂ)) :=
      inferInstanceAs (IsIso (Spec.map (starRingAut (R := ℂ)).toCommRingCatIso.hom))
    change y ≫ q = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ q = _
    rw [e, Category.assoc, cancel_epi]

theorem mem_unitaryGroup_of_norm_mulVec {α : Type*} [Fintype α] [DecidableEq α] {V : Matrix α α ℂ}
    (h : ∀ w : α → ℂ, √(∑ i, ‖V.mulVec w i‖ ^ 2) = √(∑ i, ‖w i‖ ^ 2)) : V ∈ Matrix.unitaryGroup α ℂ := by
  have key := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin V)).1 fun x => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h x.ofLp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := key (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm, Pi.single_apply, eq_comm] using this

theorem exists_unitary_of_frameNorm_conj {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (h : ∀ x : Fin N → ℂ, frameNorm M' (fun j => conj (x j)) = frameNorm M x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, M' = M.map (starRingEnd ℂ) * U := by
  have hV : M'⁻¹ * M.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mem_unitaryGroup_of_norm_mulVec fun w => by
      have := h (M.mulVec fun j => conj (w j))
      have e : (fun j => conj (M.mulVec (fun j => conj (w j)) j)) = (M.map (starRingEnd ℂ)).mulVec w :=
        funext fun j => by simp [Matrix.mulVec, dotProduct]
      rw [e, frameNorm, frameNorm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul M hM.isUnit, Matrix.one_mulVec] at this
      simpa only [RCLike.norm_conj] using this
  refine ⟨_, Unitary.star_mem hV, ?_⟩
  have e : M.map (starRingEnd ℂ) = M' * (M'⁻¹ * M.map (starRingEnd ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M' hM'.isUnit, Matrix.one_mul]
  generalize M'⁻¹ * M.map (starRingEnd ℂ) = V at e hV
  rw [e, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hV, Matrix.mul_one]

variable {F : Type} [Field F] [NumberField F]

theorem Adelic.HermSys.isConj_weight (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hc : T.ConjInvariant) (σ : F →+* ℂ) :
    (T.weight hb hh σ).IsConj (T.weight hb hh (ComplexEmbedding.conjugate σ)) := by
  obtain ⟨U, hU, e⟩ := exists_unitary_of_frameNorm_conj (hh σ) (hh (ComplexEmbedding.conjugate σ)) (hc σ)
  exact Weight.isConj_fsBasis_of_unitary _ _ _ _ _ hU e

namespace HilbertSamuel.Geo

variable (G : Geo F)

theorem isConj_φ (σ : F →+* ℂ) : (G.φ σ).IsConj (G.φ (ComplexEmbedding.conjugate σ)) :=
  G.isConj_weight _ _ G.conj σ

theorem isConj_φ₂ (σ : F →+* ℂ) : (G.φ₂ σ).IsConj (G.φ₂ (ComplexEmbedding.conjugate σ)) :=
  G.second.isConj_weight _ _ G.conj₂ σ

theorem isConj_φTw (m : ℤ) (σ : F →+* ℂ) : (G.φTw m σ).IsConj (G.φTw m (ComplexEmbedding.conjugate σ)) :=
  (G.isConj_φ₂ σ).tens ((G.isConj_φ σ).zpow m)

variable {G}

end HilbertSamuel.Geo

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsConjOfCharpolyEq
section
open Matrix Polynomial

namespace GlobalTheory.SemilocalConj

open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

theorem exists_isUnit_det_krylov {A : Type} [CommRing A] [Finite (MaximalSpectrum A)] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem exists_units_conj_of_charpoly_eq (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ)
    (M₀ M : Matrix (Fin n) (Fin n) A) (hs : M₀.charpoly.Separable) (hχ : M.charpoly = M₀.charpoly) :
    ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P := by
  have hs' : M.charpoly.Separable := hχ ▸ hs
  obtain ⟨w, hw⟩ := exists_isUnit_det_krylov M₀ hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_krylov M hs'
  obtain ⟨a, ha⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hw
  obtain ⟨b, hb⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  have h1 := GlobalTheory.Orb.mul_krylov_eq M₀ w
  have h2 := GlobalTheory.Orb.mul_krylov_eq M v
  rw [← ha] at h1
  rw [← hb, hχ] at h2
  have h3 : ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀ =
      GlobalTheory.Orb.companionMat n M₀.charpoly * ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) := by
    calc ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀
        = (↑a⁻¹ * M₀ * ↑a) * ↑a⁻¹ := by rw [mul_assoc _ (a : Matrix (Fin n) (Fin n) A), Units.mul_inv, mul_one]
      _ = ↑a⁻¹ * (↑a * GlobalTheory.Orb.companionMat n M₀.charpoly) * ↑a⁻¹ := by rw [mul_assoc (↑a⁻¹) M₀, h1]
      _ = GlobalTheory.Orb.companionMat n M₀.charpoly * ↑a⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨b * a⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, h2, mul_assoc, h3, mul_assoc]

example : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ) (M₀ M : Matrix (Fin n) (Fin n) A),
    M₀.charpoly.Separable → M.charpoly = M₀.charpoly →
      ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P :=
  exists_units_conj_of_charpoly_eq

end GlobalTheory.SemilocalConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RestrSchA

variable {κ₁ κ : Type} {j : κ₁ → κ}

theorem extend_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (φ : M → N) (h0 : φ 0 = 0)
    (y : κ₁ → M) : (fun i => φ (Function.extend j y 0 i)) = Function.extend j (fun a => φ (y a)) 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, h0]

theorem extend_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (y z : κ₁ → M) :
    Function.extend j (y + z) 0 = Function.extend j y 0 + Function.extend j z 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_smul {R M : Type} [Zero M] [SMulZeroClass R M] (hj : Function.Injective j) (c : R) (y : κ₁ → M) :
    Function.extend j (c • y) 0 = c • Function.extend j y 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem continuous_extend {M : Type} [TopologicalSpace M] [Zero M] (hj : Function.Injective j) :
    Continuous (fun y : κ₁ → M => Function.extend j y 0) := by
  refine continuous_pi fun i => ?_
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp only [hj.extend_apply]
    exact continuous_apply a
  · simp only [Function.extend_apply' _ _ _ h]
    exact continuous_const

theorem isClosedEmbedding_extend {M : Type} [TopologicalSpace M] [Zero M] [T2Space M] (hj : Function.Injective j) :
    Topology.IsClosedEmbedding (fun y : κ₁ → M => Function.extend j y 0) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : κ → M => x ∘ j)
    (fun y => by funext a; simp [hj.extend_apply]) (by fun_prop) (continuous_extend hj)

end GlobalTheory.RestrSchA

namespace GlobalTheory.RestrSchA

open scoped Classical

variable {κ₁ κ : Type} {j : κ₁ → κ}

def extL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (hj : Function.Injective j) :
    (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' y z := extend_add hj y z
  map_smul' c y := extend_smul hj c y
  cont := continuous_extend hj

theorem norm_le_extL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ₁] [Fintype κ]
    (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖extL V hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : extL V hj y (j a) = y a := by simp [extL, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm _ _

def restrS (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j) :
    SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ₁ → NumberField.mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (extL (NumberField.mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_extL hj y
      have h0 := norm_nonneg (extL (NumberField.mixedEmbedding.mixedSpace F) hj y)
      simp only [pow_one, one_mul]
      linarith⟩

theorem restrS_apply (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (y : κ₁ → NumberField.mixedEmbedding.mixedSpace F) :
    restrS F hj f y = f (Function.extend j y 0) := by
  simp [restrS, extL]

theorem sb_comp_extend (F : Type) [Field F] [NumberField F] (hj : Function.Injective j)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y => g (Function.extend j y 0)) ∈ SB (κ₁ → FiniteAdeleRing (𝓞 F) F) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
  exact ⟨hg.1.comp_continuous (continuous_extend hj), hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend hj)⟩

theorem pureA_extend (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ₁ → AdeleRing (𝓞 F) F) :
    pureA F f g (Function.extend j y 0) = pureA F (restrS F hj f) (fun z => g (Function.extend j z 0)) y := by
  simp only [pureA, restrS_apply]
  rw [extend_map hj (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
      (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _) y,
    extend_map hj (fun x : AdeleRing (𝓞 F) F => x.2) rfl y]

theorem mem_schA_comp_extend : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  intro F _ _ κ₁ κ _ _ j hj Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨restrS F hj f, fun z => g (Function.extend j z 0), sb_comp_extend F hj hg, ?_⟩
    funext y
    exact pureA_extend F hj f g y
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.RestrSchA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section

namespace GlobalTheory.SchwartzBruhatRestrict

theorem map_funLeft_extendZero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl F, (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  intro F _ _ κ₁ κ _ _ j hj v
  classical
  set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext
  have hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext :=
    fun y => funext fun i => hj.extend_apply y 0 i
  have hcr : Continuous (fun x : κ → Fv F v => x ∘ j) :=
    continuous_pi fun i => continuous_apply (j i)
  have hce : Continuous ext := by
    refine continuous_pi fun k => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [ext, hj.extend_apply]
      exact continuous_apply i
    · simp only [ext, Function.extend_apply' _ _ _ hk]
      exact continuous_const
  have hemb : Topology.IsClosedEmbedding ext := hr.isClosedEmbedding hcr hce
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hlc, hcs⟩, rfl⟩
    exact ⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩
  · rintro φ₁ ⟨hlc, hcs⟩
    let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)) := by
      ext x
      simp only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        Valuation.mem_integer_iff]
    have hOo : IsOpen O := by rw [hOeq]; exact Valued.isOpen_integer _
    have hOc : IsClosed O := by rw [hOeq]; exact Valued.isClosed_integer _
    have hOk : IsCompact O :=
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    have hO0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
    let S : Set (κ → Fv F v) := {x | ∀ k, k ∉ Set.range j → x k ∈ O}
    have hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O := by
      ext x; simp [S]
    have hSo : IsOpen S := by
      rw [hSeq]
      exact Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)
    have hSc : IsClosed S := by
      rw [hSeq]
      exact isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)
    set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg
    have hglc : IsLocallyConstant g := hlc.comp_continuous hcr
    refine ⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]
      · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · let C : κ → Set (Fv F v) := fun k =>
        if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O
      have hC : IsCompact (Set.univ.pi C) := by
        refine isCompact_univ_pi fun k => ?_
        by_cases h : k ∈ Set.range j
        · simp only [C, dif_pos h]
          exact hcs.isCompact.image (continuous_apply _)
        · simp only [C, dif_neg h]
          exact hOk
      refine HasCompactSupport.intro hC fun x hx => ?_
      by_contra hne
      have hxS : x ∈ S := by
        by_contra hxS; exact hne (Set.indicator_of_notMem hxS _)
      have hgx : g x ≠ 0 := by rwa [Set.indicator_of_mem hxS] at hne
      apply hx
      intro k _
      by_cases h : k ∈ Set.range j
      · simp only [C, dif_pos h]
        refine ⟨x ∘ j, subset_tsupport _ hgx, ?_⟩
        simp only [Function.comp_apply]
        rw [Classical.choose_spec h]
      · simp only [C, dif_neg h]
        exact hxS k h
    · funext y
      rw [LinearMap.funLeft_apply]
      have hyS : ext y ∈ S := by
        intro k hk
        have hk' : ¬ ∃ i, j i = k := hk
        simp only [ext, Function.extend_apply' _ _ _ hk']
        exact hO0
      rw [Set.indicator_of_mem hyS]
      exact congrArg φ₁ (hr y)

end GlobalTheory.SchwartzBruhatRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationMapEquivariant
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.Equivariance

lemma mul_prod_ofFn {A ι : Type} [Ring A] [Algebra ℂ A] [Fintype ι] (X : ι → A) (z : A) (c : ι → ι → ℂ)
    (h : ∀ x, z * X x = X x * z + ∑ y, c y x • X y) (k : ℕ) (g : Fin k → ι) :
    z * (List.ofFn fun i => X (g i)).prod = (List.ofFn fun i => X (g i)).prod * z +
      ∑ i, ∑ y, c y (g i) • (List.ofFn fun j => X (Function.update g i y j)).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ (i : Fin k) (y : ι) (j : Fin k), Function.update g i.succ y j.succ =
        Function.update (fun j : Fin k => g j.succ) i y j := by
      intro i y j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne (fun h' => hj (Fin.succ_injective _ h'))]
    have e0 : ∀ (y : ι) (j : Fin k), Function.update g 0 y j.succ = g j.succ := fun y j =>
      Function.update_of_ne (Fin.succ_ne_zero j) _ _
    have e1 : ∀ (i : Fin k) (y : ι), Function.update g i.succ y 0 = g 0 := fun i y =>
      Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, e, e0, e1, Function.update_self]
    rw [← mul_assoc, h, add_mul, mul_assoc, ih (fun j => g j.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

variable {R S : ℕ}

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  obtain ⟨⟨a, b⟩, hab⟩ := x
  ext c d
  have hab' : ¬ sameBlock a b := hab
  have hl : (Z * eNC ⟨(a, b), hab⟩ - eNC ⟨(a, b), hab⟩ * Z) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
    simp only [eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
    congr 1
    · by_cases h : d = b
      · subst h; simp
      · simp [h, Ne.symm h]
    · by_cases h : c = a
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [hl, Matrix.sum_apply]
  by_cases hcd : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · have h1 : Z c a * (if d = b then 1 else 0) = 0 := by
        by_cases h : d = b
        · subst h
          rw [hZ c a, zero_mul]
          clear hl hab
          rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      have h2 : (if c = a then 1 else 0) * Z b d = 0 := by
        by_cases h : c = a
        · subst h
          rw [hZ b d, mul_zero]
          clear h1 hl hab
          rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      rw [h1, h2, sub_zero]
    · rintro ⟨⟨u, v⟩, huv⟩ _
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact huv hcd
      simp [eNC, Eab, Matrix.single_apply, this]
  · rw [Finset.sum_eq_single (⟨(c, d), hcd⟩ : NC R S)]
    · simp [eNC, Eab, adP]
    · rintro ⟨⟨u, v⟩, huv⟩ _ hne
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [eNC, Eab, Matrix.single_apply, this]
    · simp

lemma sum_update_swap {ι B : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid B] {k : ℕ} (i : Fin k)
    (F : (Fin k → ι) → (Fin k → ι) → ι → ι → B) :
    ∑ g, ∑ x, F g (Function.update g i x) (g i) x = ∑ g, ∑ y, F (Function.update g i y) g y (g i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
    (fun p => (Function.update p.1 i p.2, p.1 i)) ?_ ?_ ?_ ?_ ?_ <;> simp

theorem phiN_tAct : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V) (hN : KStable M.act N) (k : ℕ) (Z : Mat R S),
    IsKC Z → ∀ Ψ : (Fin k → NC R S) → N,
      phiN M.act N k (tAct k (restrAct M.act N hN) Z Ψ) = M.act Z (phiN M.act N k Ψ) := by
  intro R S M N hN k Z hZ Ψ
  have h : ∀ x : NC R S, M.act Z * M.act (eNC x) =
      M.act (eNC x) * M.act Z + ∑ y, adP Z y x • M.act (eNC y) := by
    intro x
    have h1 := M.lie Z (eNC x)
    rw [bracket_eNC hZ, map_sum] at h1
    simp only [map_smul] at h1
    rw [h1]; abel
  have hw : ∀ (g : Fin k → NC R S) (v : M.V), M.act Z (word M.act g v) = word M.act g (M.act Z v) +
      ∑ i, ∑ y, adP Z y (g i) • word M.act (Function.update g i y) v := by
    intro g v
    have := congrArg (fun T : Module.End ℂ M.V => T v)
      (mul_prod_ofFn (fun x => M.act (eNC x)) (M.act Z) (adP Z) h k g)
    simpa [word, LinearMap.sum_apply] using this
  simp only [phiN_apply, tAct_apply, map_sum, hw, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    restrAct_apply, kpart_of_isKC hZ, map_add, map_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_update_swap i (fun g g' y x => adP Z y x • word M.act g (Ψ g' : M.V))

end GlobalTheory.SteepMult.Equivariance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeriesStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank), IsONFr X x → IsInvOf W hr X x s → IsBasOf W hr X hq x BW → IsVarOf V W X q0 vr → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW f (MvPolynomial.rename vr P) 0 = ((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P x := by
  first | exact @GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP | exact GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP | (intros; apply GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP <;> assumption)
end

