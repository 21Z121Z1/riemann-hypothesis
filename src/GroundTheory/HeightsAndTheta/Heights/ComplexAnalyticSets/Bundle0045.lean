import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametrisationSheetsConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter MeasureTheory

theorem exists_clm_ne_zero_of_countable {σ : Type} [Fintype σ] {T : Set (σ → ℂ)} (hT : T.Countable)
    (h0 : (0 : σ → ℂ) ∉ T) : ∃ ℓ : (σ → ℂ) →L[ℂ] ℂ, ∀ u ∈ T, ℓ u ≠ 0 := by
  classical
  let φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ) := fun u =>
    { toFun := fun v => ∑ i, v i * u i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u v, φ u v = ∑ i, v i * u i := fun _ _ => rfl
  have hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0 := by
    intro u hu
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rwa [show u = 0 from funext h] at hu)
    have hm : Pi.single i 1 ∈ LinearMap.ker (φ u) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at hm
    simp [Pi.single_apply] at hm
    exact hi hm
  have hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0 :=
    (measure_biUnion_null_iff hT).2 hker
  obtain ⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by
    by_contra h
    push Not at h
    have hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := fun x _ => h x
    have hpos := isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty
    exact hpos.ne' (measure_mono_null hu hnull)
  refine ⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩
  have hvu : φ u v ≠ 0 := fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))
  rw [hφ] at hvu
  simpa [ContinuousLinearMap.sum_apply] using hvu

theorem ParametrisationSheetsConnected.proof (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmooth
section
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem formallySmooth_of_perfectField_of_charP [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] :
    Algebra.FormallySmooth F K := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ N hN u => ?_
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap F B), CharP.cast_eq_zero, map_zero]
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  have hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p := fun z c hc => by
    show P (u z) = c ^ p
    rw [← hc, sqZeroFrobeniusLift_mk]
  obtain ⟨σ₀, hσ₀⟩ := exists_isGoodPartialLift_frobenius (K := K) p hpB hN u
  have : Nonempty {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} :=
    ⟨⟨σ₀, hσ₀⟩⟩
  obtain ⟨⟨⟨L, φ⟩, hgood⟩, hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (r := fun a b : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} =>
      PartialLiftLE a.1 b.1)
    (exists_isGoodPartialLift_upperBound (p := p) (N := N) (u := u) (ψ := ψ)) (fun hab hbd => hab.trans hbd)
  have htop : (⊤ : IntermediateField F K) ≤ L := by
    intro x _
    by_contra hx
    obtain ⟨σ, hσ, hle, hxσ⟩ := exists_isGoodPartialLift_extend p hψ hgood hx
    exact hx ((hm ⟨σ, hσ⟩ hle).1 hxσ)
  refine ⟨φ.comp ((IntermediateField.inclusion htop).comp IntermediateField.topEquiv.symm.toAlgHom), ?_⟩
  ext x
  exact hgood.2 _

theorem formallySmooth_of_charZero [CharZero F] : Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  have := hs.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact .of_algebraicIndependent_of_isSeparable hs.1

end

theorem PerfectFieldExtensionFormallySmooth.proof : PerfectFieldExtensionFormallySmooth.Statement := by
  intro F K _ _ _ _
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := Fact.mk hp
    exact formallySmooth_of_perfectField_of_charP p
  · have := CharP.charP_to_charZero F
    exact formallySmooth_of_charZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyDerivationsDetectSquare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

open IsLocalRing KaehlerDifferential TensorProduct

theorem PolyDerivationsDetectSquare.of_perfectField
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical

  have : Algebra.FormallySmooth F k := h₁ F k
  have : Algebra.FormallySmooth F p.ResidueField := h₁ F p.ResidueField
  have : Algebra.FormallySmooth F (MvPolynomial (Fin n) k) :=
    Algebra.FormallySmooth.comp F k (MvPolynomial (Fin n) k)
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨ret, hret⟩ := (Algebra.FormallySmooth.iff_split_injection (R := F)
    (P := Localization.AtPrime p) hsurj).mp inferInstance
  have hinj : Function.Injective (kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField) :=
    Function.LeftInverse.injective (g := ret) fun x => LinearMap.congr_fun hret x
  have hgI : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hg

  have : Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F] := h₂ F k n
  let b := Module.Free.chooseBasis (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F]
  have hc : ∀ α, b.repr (D F (MvPolynomial (Fin n) k) g) α ∈ p := fun α =>
    hD (((b.coord α).compDer (D F (MvPolynomial (Fin n) k))).restrictScalars ℤ)

  have hzero : kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField
      (Ideal.toCotangent _ ⟨_, hgI⟩) = 0 := by
    change (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime p]
      D F (Localization.AtPrime p) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g) = 0
    rw [← map_D F F (MvPolynomial (Fin n) k) (Localization.AtPrime p),
      ← b.linearCombination_repr (D F (MvPolynomial (Fin n) k) g), Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.sum, tmul_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.map_smul, ← algebraMap_smul (Localization.AtPrime p), tmul_smul,
      ← algebraMap_smul p.ResidueField, ← IsScalarTower.algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr (hc α), zero_smul]
  have h0 := hinj (hzero.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
      maximalIdeal (Localization.AtPrime p) := IsLocalRing.ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  rw [← hker]
  exact h0

theorem PolyDerivationsDetectSquare.proof (h₁ : PerfectFieldExtensionFormallySmooth.Statement)
    (h₂ : PolyKaehlerFree.Statement) : PolyDerivationsDetectSquare.Statement := by
  intro k _ n p _ g hg hD
  obtain ⟨q, hq⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k q with hqp | rfl
  · have : Fact q.Prime := ⟨hqp⟩
    let _ : Algebra (ZMod q) k := ZMod.algebra k q
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ (ZMod q) k n p g hg hD
  · have : CharZero k := CharP.charP_to_charZero k
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ ℚ k n p g hg hD

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem graphPt_injective {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this

theorem differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i

theorem continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem ProjectionFormula.proof (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem IsRegularPointOf.exists_ball_chart {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by
  obtain ⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩ := hz
  have hzO : z ∈ g '' O := by rw [← hYV]; exact ⟨hzY, hzV⟩
  obtain ⟨y₀, hy₀O, rfl⟩ := hzO
  have hN : interior W ∩ V ∈ 𝓝 (g y₀) := inter_mem (interior_mem_nhds.2 hW) (hV.mem_nhds hzV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hO.mem_nhds hy₀O) ((hg y₀ hy₀O).continuousAt.preimage_mem_nhds hN))
  refine ⟨d, V ∩ interior W ∩ A ⁻¹' Metric.ball y₀ r, Metric.ball y₀ r, g,
    (hV.inter isOpen_interior).inter (Metric.isOpen_ball.preimage A.continuous),
    ⟨⟨hzV, mem_interior_iff_mem_nhds.2 hW⟩, ?_⟩, fun x hx => interior_subset hx.1.2,
    Metric.isOpen_ball, (convex_ball y₀ r).isPreconnected, fun y hy => hg y (hball hy).1, ?_⟩
  · show A (g y₀) ∈ Metric.ball y₀ r
    rw [hAg y₀ hy₀O]
    exact Metric.mem_ball_self hr
  · ext x
    constructor
    · rintro ⟨hxY, ⟨hxV, -⟩, hxB⟩
      have hx : x ∈ g '' O := by rw [← hYV]; exact ⟨hxY, hxV⟩
      obtain ⟨y, hyO, rfl⟩ := hx
      have hyB : A (g y) ∈ Metric.ball y₀ r := hxB
      rw [hAg y hyO] at hyB
      exact ⟨y, hyB, rfl⟩
    · rintro ⟨y, hyB, rfl⟩
      have hyO : y ∈ O := (hball hyB).1
      have hyN : g y ∈ interior W ∩ V := (hball hyB).2
      have hgy : g y ∈ Y ∩ V := by rw [hYV]; exact ⟨y, hyO, rfl⟩
      refine ⟨hgy.1, ⟨hyN.2, hyN.1⟩, ?_⟩
      show A (g y) ∈ Metric.ball y₀ r
      rw [hAg y hyO]
      exact hyB

theorem eq_zero_on_chart_of_eventually_eq_zero {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by
  obtain ⟨y, hy, hyF⟩ := h0
  have hgB : ∀ t ∈ B, g t ∈ Y ∩ V := fun t ht => by rw [hYV]; exact ⟨t, ht, rfl⟩
  have hy' : y ∈ g '' B := by rw [← hYV]; exact hy
  obtain ⟨t₀, ht₀, rfl⟩ := hy'
  have hFg : AnalyticOnNhd ℂ (F ∘ g) B := fun t ht => (hF (g t) (hgB t ht).2).comp (hg t ht)
  have hev : F ∘ g =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [(hg t₀ ht₀).continuousAt.tendsto.eventually hyF, hBo.mem_nhds ht₀] with t ht htB
    exact ht (hgB t htB).1
  have hzero := hFg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc ht₀ hev
  intro u hu
  have hu' : u ∈ g '' B := by rw [← hYV]; exact hu
  obtain ⟨t, ht, rfl⟩ := hu'
  exact hzero ht

theorem RegularLocusIdentity.proof (hreg : RegularOffHypersurface.Statement) :
    RegularLocusIdentity.Statement := by
  intro σ _ I hI
  obtain ⟨h, hhI, hh⟩ := hreg σ I hI
  refine ⟨h, hhI, fun z hz hhz W hW => ?_⟩
  obtain ⟨d, V, B, g, hVo, hzV, hVW, hBo, hBc, hg, hYV⟩ := (hh z hz hhz).exists_ball_chart hW
  exact ⟨V, hVo, hzV, hVW, fun F hF h0 => eq_zero_on_chart_of_eventually_eq_zero hBo hBc hg hYV F hF h0⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem SerreRFlatAscent.proof : SerreRFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hRA hfib P _ hdim
  have : IsNoetherianRing A := hA
  have : IsNoetherianRing B := hB
  have : Module.Flat A B := hflat
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have := isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)
  let e := Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A))
    (S := Localization.AtPrime P)
  have h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A)) :=
    ringKrullDim_nonneg_of_nontrivial
  have h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hsum] at hdim
  have hAk := (le_add_of_nonneg_right h0F).trans hdim
  have hFk := (le_add_of_nonneg_left h0A).trans hdim
  have hF : IsRegularLocalRing (primeFibreLocalRing A P) :=
    hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)
  exact isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

