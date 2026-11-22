import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SegreFlagCutSection.proof (hModel : SegreFlagClosureModel.Statement)
    (hForms : SegreFlagCutForms.Statement) (hDiv : SegreFlagCutDivisor.Statement)
    (hD0 : SegreFlagDegreeZero.Statement) : SegreFlagCutSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk r a ha
  classical
  set I := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hI
  have hIp : I.IsPrime := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht (k + 1) (Nat.le_add_left 1 k) hk).1.multiProj.isPrime
  have hpt : ∀ (j : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t j ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl
  have hlift : ∀ i, liftPairForm M M' (a i) ∉ I := fun i hm =>
    ha i ((liftPairForm_mem_iff (hpt (k + 1)) _).1 hm)
  obtain ⟨f₃, g₃, hD₃, hv₃, hk₃⟩ := hD0 O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk

  let bad : MRing (bundleIdx (bundleIdx ι M) M') O → Set (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) :=
    fun z => {Q | Q ∈ (I ⊔ Ideal.span {z}).minimalPrimes ∧ IsRelevant Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q}
  let T := bad f₃ ∪ bad g₃ ∪ ⋃ i, bad (liftPairForm M M' (a i))
  have hbfin : ∀ z, (bad z).Finite := fun z =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I ⊔ Ideal.span {z})).subset fun Q hQ => hQ.1
  have hTfin : T.Finite := ((hbfin _).union (hbfin _)).union (Set.finite_iUnion fun i => hbfin _)
  have hbad : ∀ z, ∀ Q ∈ bad z, Q.IsPrime ∧ IsRelevant Q ∧ I ≤ Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q :=
    fun z Q hQ => ⟨hQ.1.1.1, hQ.2.1, le_sup_left.trans hQ.1.1.2, hQ.2.2⟩
  obtain ⟨cs, ch, s, h, hs, hh, hdeg, hsI, hhI, hval, havoid⟩ :=
    hForms O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      hTfin.toFinset (by
        intro Q hQ
        rcases (hTfin.mem_toFinset.1 hQ) with (hQ | hQ) | hQ
        · exact hbad _ Q hQ
        · exact hbad _ Q hQ
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hQ
          exact hbad _ Q hi)
  have hdiv := hDiv O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
    cs ch s h hs hh hdeg hsI hhI hval
  refine ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsI, hhI, hval, hdiv, hD₃, hv₃, hk₃, ?_⟩
  intro H hH hϖH
  by_cases hh0 : divCycle I h H = 0
  ·
    have hs0 : divCycle I s H ≠ 0 := hH.resolve_right (not_not.2 hh0)
    have hne : ratDiv I s h H ≠ 0 := by
      unfold ratDiv
      rw [hh0, sub_zero]
      exact hs0
    rw [hdiv H hϖH] at hne
    split_ifs at hne with hc
    · obtain ⟨hk0, rfl⟩ := hc
      obtain ⟨hf, hg, -⟩ := hk₃ hk0
      exact ⟨hf, hg, fun i hm => ha i ((liftPairForm_mem_iff (hpt k) _).1 hm)⟩
    · exact absurd rfl hne
  ·
    obtain ⟨hmin, hrel⟩ := relevant_minimal_of_divCycle_ne_zero hh0
    have hhH : h ∈ H := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    have avoid : ∀ z, z ∉ I → (H ∈ bad z → H ∈ T) → z ∉ H := by
      intro z hz hT hzH
      exact havoid H (hTfin.mem_toFinset.2 (hT ⟨mem_minimalPrimes_sup_span_of_mem hmin hz hzH, hrel, hϖH⟩)) hhH
    exact ⟨avoid f₃ hD₃.num_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_left _ h'),
      avoid g₃ hD₃.den_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_right _ h'),
      fun i => avoid _ (hlift i) fun h' => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, h'⟩)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def flagCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B)
    (k : ℕ) : Fin N → B :=
  fun j => if (j : ℕ) < k then ∑ i, u i * algebraMap Ω B (w.repr (e i) j) else 0

def pairCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (u : Fin N → B) : (Σ o, bundleIdx (bundleIdx ι M) M' o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ' l (w i))
  | ⟨some o, j⟩ => projCoordRing y w φ u ⟨o, j⟩

theorem flagCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B) (k : ℕ) :
    g ∘ flagCoordRing w e u k = flagCoordRing w e (g ∘ u) k := by
  funext j
  by_cases hj : (j : ℕ) < k <;> simp [flagCoordRing, hj, map_sum]

theorem pairCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    g (pairCoordRing y w φ φ' u p) = pairCoordRing y w φ φ' (g ∘ u) p := by
  rcases p with ⟨_ | o, l⟩
  · simp [pairCoordRing, map_sum]
  · simp only [pairCoordRing]
    exact projCoordRing_map g y w φ u _

theorem flagCoord_eq_flagCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (w e : Module.Basis (Fin N) Ω E)
    (t : Fin N → Φ) (k : ℕ) : flagCoord w e t k = flagCoordRing w e t k := rfl

theorem pairProjCoord_eq_pairCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) : pairProjCoord y w φ φ' t = pairCoordRing y w φ φ' t := by
  funext p
  rcases p with ⟨_ | o, l⟩
  · rfl
  · simp only [pairProjCoord, pairCoordRing]
    rw [projCoord_eq_projCoordRing]

theorem aeval_flagSub_sigma (w e : Module.Basis (Fin N) Ω E) (k j : Fin N) :
    aeval (fun i => X i - (∑ m, X m * C (w.repr (e m) k)) * C (e.repr (w k) i))
        (∑ i, X i * C (w.repr (e i) j) : MvPolynomial (Fin N) Ω) =
      (∑ i, X i * C (w.repr (e i) j)) - if k = j then ∑ i, X i * C (w.repr (e i) k) else 0 := by
  set S : MvPolynomial (Fin N) Ω := ∑ m, X m * C (w.repr (e m) k) with hS
  have hsum : ∑ i, e.repr (w k) i * w.repr (e i) j = if k = j then 1 else 0 := by
    have h := congrArg (fun v => w.repr v j) (e.sum_repr (w k))
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h
    rw [h]
  have hx : ∀ x, aeval (fun i => X i - S * C (e.repr (w k) i)) (X x * C (w.repr (e x) j)) =
      X x * C (w.repr (e x) j) - S * C (e.repr (w k) x * w.repr (e x) j) := by
    intro x
    rw [map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, sub_mul, map_mul, mul_assoc]
  rw [map_sum, Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum]
  split_ifs with h
  · subst h; rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

end Ring

theorem SegreFlagCutSpecialize.proof : SegreFlagCutSpecialize.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' _ _ Φ _ _ _ _ e t ht
    k hk
  classical
  let ev : (MvPolynomial (Fin N) Ω) →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let kk : Fin N := ⟨k, hk⟩
  let sub : (MvPolynomial (Fin N) Ω) →ₐ[Ω] (MvPolynomial (Fin N) Ω) := aeval fun i => X i - (∑ m, X m * C (w.repr (e m) kk)) * C (e.repr (w kk) i)
  have hevF : ∀ j : ℕ, ev ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) j = flagCoordRing w e t j := by
    intro j
    rw [flagCoordRing_map]
    congr 1
    funext i
    simp [ev, aeval_X]
  have hsubF : sub ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) = flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) k := by
    funext j
    have hs := aeval_flagSub_sigma w e kk j
    simp only [Function.comp_apply, flagCoordRing]
    rcases lt_trichotomy (j : ℕ) k with h | h | h
    · have hkj : kk ≠ j := fun h' => by rw [← h'] at h; exact lt_irrefl _ h
      rw [if_pos (by omega), if_pos h]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_neg hkj, sub_zero]
    · have hkj : kk = j := Fin.ext h.symm
      rw [if_pos (by omega), if_neg (by omega)]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_pos hkj, hkj, sub_self]
    · rw [if_neg (by omega), if_neg (by omega), map_zero]
  let cA : ℕ → (Σ o, bundleIdx (bundleIdx ι M) M' o) → (MvPolynomial (Fin N) Ω) :=
    fun j => pairCoordRing y w φ φ' (flagCoordRing w e X j)
  have hcoord : ∀ j : ℕ, flagClosurePt y w e φ φ' t j = fun p => ev (cA j p) := by
    intro j
    funext p
    simp only [cA, flagClosurePt, pairProjCoord_eq_pairCoordRing, flagCoord_eq_flagCoordRing, pairCoordRing_map,
      hevF]
  have hsubc : ∀ p, sub (cA (k + 1) p) = cA k p := by
    intro p
    simp only [cA]
    rw [pairCoordRing_map, hsubF]
  let algA : O →+* (MvPolynomial (Fin N) Ω) := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap O Ω)
  have hevA : (ev : (MvPolynomial (Fin N) Ω) →+* Φ).comp algA = algebraMap O Φ :=
    RingHom.ext fun a => by simp [algA, ← IsScalarTower.algebraMap_apply]
  have hsubA : (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)).comp algA = algA := RingHom.ext fun a => by simp [algA]
  refine ⟨fun s hs => ?_, fun s h hsh => ?_⟩
  · have key : ∀ j : ℕ, pointConeMap O (flagClosurePt y w e φ φ' t j) s =
        map (ev : (MvPolynomial (Fin N) Ω) →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) s) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      simp only [pointConeMap, aeval_def, MvPolynomial.algebraMap_eq]
      rfl
    have ksub : map (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)) (eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s) =
        eval₂ (C.comp algA) (fun p => C (cA k p) * X p.1) s := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [pointIdeal, RingHom.mem_ker] at hs ⊢
    rw [key] at hs ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s = 0 :=
      map_injective _ hev (hs.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx (bundleIdx ι M) M') O),
        aeval (flagClosurePt y w e φ φ' t j) v = ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [aeval_def, ← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx (bundleIdx ι M) M') O,
        sub (eval₂ algA (cA (k + 1)) v) = eval₂ algA (cA k) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    let τA : (MvPolynomial (Fin N) Ω) := ∑ j, flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) j * algebraMap Ω (MvPolynomial (Fin N) Ω) (w'.repr (w j) kk)
    have hτ : flagLineCoord w' w e t (k + 1) kk = ev τA := by
      simp only [τA, flagLineCoord, map_sum, map_mul, AlgHom.commutes, flagCoord_eq_flagCoordRing, ← hevF,
        Function.comp_apply]
    have hsubτ : sub τA = 0 := by
      simp only [τA, map_sum, map_mul, AlgHom.commutes]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj := congrFun hsubF j
      simp only [Function.comp_apply] at hj
      rw [hj]
      by_cases hjk : (j : ℕ) < k
      · rw [repr_flag_inv w w' hF.sameFlag j kk (Fin.lt_def.mpr hjk), map_zero, mul_zero]
      · simp [flagCoordRing, hjk]
    rw [val, val, hτ] at hsh
    have hs' : eval₂ algA (cA (k + 1)) s = τA * eval₂ algA (cA (k + 1)) h :=
      hev (by rw [hsh, map_mul])
    rw [val, ← vsub, hs', map_mul, hsubτ, zero_mul, map_zero]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagVertSymmIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem le_of_mem_ratCyc_support {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    (hW : W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support) : P ≤ W := by
  have key : ∀ s, ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0 → P ≤ W := by
    intro s hs
    by_contra hPW
    apply hs
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    exact hPW (le_trans le_sup_left hmin.1.2)
  rw [Finsupp.mem_support_iff] at hW
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0
  · by_cases hg : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W = 0
    · simp [hf, hg] at hW
    · exact key g hg
  · exact key f hf

theorem FullFlagVerticalSymmetric.proof (hFib : VerticalDivisorFibreVariety.Statement)
    (hRes : FullFlagRestriction.Statement)
    (hSeg : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
      (ι : K → Type) [∀ k, Fintype (ι k)], IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι) :
    FullFlagVerticalSymmetric.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B hM fl₁ fl₂ I hI G hG n Y R b f g hD
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  congr 1
  have hV := hFib O K ι _ d hM b f g hD W hW
  have : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).IsPrime := hV.1.1
  obtain ⟨hmc, B', -, hfl⟩ := hRes O Ω K ι x d N V B hM (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) hV.1
    (Ideal.map_mono (le_of_mem_ratCyc_support hW))
  obtain ⟨fl₁', h₁, -⟩ := hfl fl₁
  obtain ⟨fl₂', h₂, -⟩ := hfl fl₂
  have hV' : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W))) d := by
    rw [hmc]
    exact hV
  have := SegreFlagIndep.segreFlagIndep_homogeneous_implies_general _ _ ι (hSeg (IsLocalRing.ResidueField O) _ K ι)
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W)) d hV' N _ B' fl₁' fl₂' I hI G hG n Y R
  rw [hmc, h₁, h₂] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

