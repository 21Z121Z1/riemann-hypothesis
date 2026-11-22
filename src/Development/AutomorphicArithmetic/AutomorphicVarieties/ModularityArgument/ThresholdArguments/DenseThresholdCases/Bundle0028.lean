import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT UpperTheory.V.Z.Bc
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
private theorem upCycI (hP : _root_.UpperTheory.V.Af.Hypotheses') (hL : CyclicBaseChangeLiftRankTwo) (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E]
    [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hp : (Module.finrank F E).Prime) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (π : CuspSub F 2) (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hatt : AttC ι r π) (hirr : IsIrr (r.comp (galEmb F E Ω))) :
    ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  rcases hL F E hp π hreg with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hP F Ω l ι 2 r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ 2 r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr, ?_⟩, hinf⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 2 r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π)
    (hi : IsIrr (r.comp (galEmb F E Ω))) : ∃ P : CuspSub E n, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  obtain ⟨-, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩, fun τ m hm => by
      have h := (UpperTheory.V.FieldIso.hasInfChar_pullSub j π _ m).2 hm
      rwa [show (τ.comp (algebraMap F E)).comp (j : E →+* F) = τ from RingHom.ext fun x => congrArg τ (j.symm_apply_apply x)] at h⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
theorem UpperTheory.V.Z.Bc.upSolI_of_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → CyclicBaseChangeLiftRankTwo → UpSolI := by
  intro P hL F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r π hc hreg ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι 2 r π hreg ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  obtain ⟨Q, q1, q2, q3⟩ := upCycI P hL F K Ω l ι (hdeg ▸ hp) r π hc hreg ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hi)
  obtain ⟨Q', p1, p2, p3⟩ := ih _ hlt K rfl _ Q (hc.comp (resFacts F K Ω l 2 r).1) q1 q2 hi
  refine ⟨Q', p1, p2, fun τ m hm => p3 τ m (q3 _ m ?_)⟩
  rwa [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
theorem UpperTheory.V.Z.Bc.upQuadI_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : QuadLiftRealToComplexRankTwo) : UpQuadI := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE r π hr hreg hatt hirr
  obtain ⟨P, hBC⟩ := (h F E hE π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion F E Ω l ι hE 2 r π hr hatt hirr η hη ht
  have h1 := UpperTheory.V.Br.bcAtt0 F E Ω l ι 2 r π P hBC
  exact ⟨P, h1.1 hreg, h1.2 hatt ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr), hBC.inf⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularDeformationQuotientRegularAtPoint
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
attribute [local instance high] DivisionSemiring.to_moduleIsTorsionFree
theorem UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
        (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
        (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
        Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
        X.LocZero J (y : X.A →+* PowerSeries k) := by
  intro _ Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ k _ _ _ y hy hyJ hU hI q hq hqy
  have hQ := P1.psPair D T c' h X k y hy
  haveI : IsLocalHom (algebraMap c'.O k) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hQ.loc a hn)⟩
  letI : Algebra (ResidueField c'.O) k := (ResidueField.lift (algebraMap c'.O k)).toAlgebra
  haveI : IsScalarTower c'.O (ResidueField c'.O) k := IsScalarTower.of_algebraMap_eq fun a => rfl
  obtain ⟨hfin, hchar, -⟩ := P1.coefRes c'
  obtain ⟨ρ, hρ, hρc⟩ := P1.rhoEx D T c' h K (PowerSeries k) _ (maximalIdeal _) (fun a ha => by
    rw [PowerSeries.algebraMap_apply, hQ.loc a ha, map_zero]; exact zero_mem _) hQ.pair hQ.cont
  obtain ⟨P, hP, hform⟩ := P1.formEx D T hF hD c' h K _ _ ρ hQ.pair hρ
  obtain ⟨ψ, hψ, hflag⟩ := P1.psiEx D T c' h K _ _ ρ hQ.pair hρ
  obtain ⟨hψr, hψc⟩ := P1.redPsi D T c' h K k _ hQ ψ hψ
  let x : W.Point K.r :=
    { K := k, ρ := ρ, cont := hρc, P := P, symm := hP, form := hform, red := P1.redDet D T c' h K k _ hQ ρ hρ
      ine := P1.ineTriv D T c' h K _ _ ρ hQ.pair hρ, ψ := ψ, ψ_red := hψr, flag := fun v => hflag _ _ v }
  obtain ⟨hne, hA⟩ := P1.condA D T hF hD c' h K _ _ ψ hψ (fun v i j hij => by
    obtain ⟨s, hs, hne⟩ := hU v i j hij
    have e := (sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P).1
    exact ⟨s, hs, fun hh => hne ((e v i s).symm.trans (hh.trans (e v j s)))⟩)
  obtain ⟨n1, n2, n3⟩ := h4 l K.s.odd K.V.frame c'.O K.r x hne hψc hA
    (P1.irrL D T c' h K x _ hQ hρ hI) (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K)
  let f : B.B →ₐ[c'.O] x.A := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hf : B.IsPt x f := P1.mapsPt D T c' h K X B φ hφ _ y ρ ψ hρ hψ
  have key := hM.p1 x f ⟨n1, n2, n3, P1.n4V0 l _ _ 4 K.r K.v0 x⟩ hf
    (fun b hb => hyJ _ (hJ ▸ Ideal.mem_map_of_mem φ hb)) ⟨q.comap φ, hq.comap φ⟩ (fun b hb => hqy _ hb)
  rw [hJ]
  exact Ideal.map_le_iff_le_comap.2 key
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmAutO
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN K.s.v0 ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hW r hr hc hm hi
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  let x : B.Pt := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hx : ∀ b, x b = y (algebraMap X.B X.A (φ b)) := fun _ => rfl
  have hJx : J₀ ≤ RingHom.ker x := fun b hb => hy _ (hJ ▸ Ideal.mem_map_of_mem φ hb)
  have hrL : (X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le) = r.comp (resQ T.L) := by
    rw [← hr]; rfl
  have hcL : Continuous (r.comp (resQ T.L)) := hc.comp (Af.continuous_restrictScalarsHom _ _ _)
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨w, hw⟩ := auArith U.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y x hx
    (auPsiCont D T c' h K X B 0 φ hφ y x hx (hrL ▸ hcL)) _ hanti hW
  have hrep := auRep D T c' h K X B 0 φ hφ y x hx
  rw [hrL, pow_zero, mul_one] at hrep
  obtain ⟨hi1, hi2⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN K.v0 hM.end2 x w _ hJx hw hrep (hi2 _)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolarOfLift
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩
private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩
private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
private theorem polar_of_lift (hP : _root_.UpperTheory.V.Af.Hypotheses') {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [Fact l.Prime] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ 2)
    (Q : CuspSub K 2) (hBC : Br.IsBC0 π Q) (hC : AttC ι (r.comp (Bc.res ℚ Ω K)) Q) (hθ : IsCycWt l wt θ) (hd : DualTw r θ) :
    ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ := by
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  have hθ' : IsCycWt l (wt + (((2 : ℕ) : ℤ) - 1))
      (θ.comp (Bc.res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (Bc.res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL 2
  have hres' : μ'.comp (Bc.res (maximalRealSubfield K) Ω K) =
      θ.comp (Bc.res ℚ Ω K) * cycBar K Ω l ^ (((2 : ℕ) : ℤ) - 1) := hres.trans rfl
  refine ⟨χ', hs, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hP.litN.aut.js.1 hP.litN.aut.gk K 2 one_le_two Q _ ?_⟩
  have hd' : DualTw (r.comp (Bc.res ℚ Ω K)) (θ.comp (Bc.res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  filter_upwards [Bc.normGal K Ω l ι χ' μ' hL', Br.bcConj0 ℚ K 2 π Q hBC, hC.2, hl] with w ⟨hu, he⟩ ⟨B, hB, hB'⟩ ⟨B₁, hB₁, hF⟩ hw
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι 2 _ _ hd' w hw B _ hF he⟩
private theorem qV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Formalism.UG.qV E w = Ideal.absNorm w.asIdeal := by
  rw [Formalism.UG.qV]
private theorem absNorm_rat {l : ℕ} (hp : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = l := by
  have hN : Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hd : Ideal.absNorm v.asIdeal ∣ l :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact v.isPrime.ne_top
private theorem sat_iff (hP : _root_.UpperTheory.V.Af.Hypotheses') {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Algebra ℚ K]
    (π : TR.CuspSub ℚ 2) (Q : CuspSub K 2) (hBC : IsBC π Q) (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion ℚ ≃+* w.adicCompletion K) (hi : IsCompl i) (B : Multiset ℂˣ) :
    π.HasSat v B ↔ (CG.mk Q).HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results hP ℚ 2 π v
  obtain ⟨⟨σ', hσ'⟩, hiso'⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results hP K 2 Q w
  have hc := hi.1
  obtain ⟨e, he⟩ := hBC.split v w i hi.1 hi.2 σ σ' hσ hσ'
  have c1 := (_root_.UpperTheory.V.Af.satake_local_of_printed_results hP ℚ 2 v σ).2 _ π.finPart (hiso σ hσ) B
  have c2 := (_root_.UpperTheory.V.Af.satake_local_of_printed_results hP K 2 w σ').2 _ Q.finPart (hiso' σ' hσ') B
  have hq : Formalism.UG.qV K w = Formalism.UG.qV ℚ v := by
    rw [qV_eq, qV_eq, GlobalTheory.LiftAbsPow.absNorm_eq i hc]
  refine ⟨fun hB => (CG.hasSat_mk _ _ _).2 (c2.2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i (GlobalTheory.LiftAbsPow.v_map_eq i hc) hq e
    (fun g x => (he g x).symm) (c1.1 hB))), fun hB => c1.2 ?_⟩
  refine GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i.symm (fun y => ?_) hq.symm e.symm (fun g x => ?_) (c2.1 ((CG.hasSat_mk _ _ _).1 hB))
  · have := GlobalTheory.LiftAbsPow.v_map_eq i hc (i.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    congr 2
    exact (Units.ext (Matrix.ext fun _ _ => (i.apply_symm_apply _)) :
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g)
end UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.base_change_split_of_printed_quad_bc :
    _root_.UpperTheory.V.Af.Hypotheses' → Z.Bc.QuadBC2 → BcSplit := by
  intro hP hQ l _ hl Ω _ _ _ ι V π hr hirr ⟨M, hM, hk⟩ hreg hatt v A hlv hv
  have hθ : IsCycWt l 0 (GlobalTheory.Ord2.dt V) := ⟨M, _, hM, hk, by rw [zpow_zero, one_mul]⟩
  have hd : DualTw V (GlobalTheory.Ord2.dt V) := dualTw_det V
  obtain ⟨K, _, _, _, _, _, _, hK, hemb, v₀, A₀, ⟨B₀, -, hB₀⟩, hA₀, s, hs, hs'⟩ := Cq.exQuad Ω l hl _ hatt.2
  have hI : IsIrr (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    isIrr_comp (range_of_sign l hK hs' ((hB₀ A₀ hA₀).1 s hs)) hirr
  obtain ⟨Q, hBC⟩ := (hQ ℚ K hK π hreg).resolve_left fun ⟨η, hη, ht⟩ => _root_.UpperTheory.V.Af.Bc.noTwist_of_prints hP ℚ K Ω l ι hK 2 V π hr hatt hI η hη ht
  have hBC0 := (Br.IsBCw.of_isBC hBC).toIsBC0
  have hC := Br.bcAtt0 ℚ K Ω l ι 2 V π Q hBC0
  have hA : AttC ι (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) Q :=
    hC.2 hatt ((Bc.irrBasic.1 _ Unit _ 2 _).2.1 hI)
  obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hv hlv
  have hjK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := fun x => by
    obtain ⟨y, hy⟩ := Cq.embPadic K hK l hemb (Bw.j.comp (algebraMap K Ω)) x
    exact (hy ▸ Bw.Kw.1.algebraMap_mem y :)
  obtain ⟨w, hw, i, hi⟩ := Cq.exPlaceIso ℚ K Ω l A v hv O Bw hj hjK
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, w, hK, hI, hC.1 hreg, polar_of_lift hP hK ι V 0 _ π Q hBC0 hA hθ hd, hA, hw, ?_, ?_, ?_,
    fun B => sat_iff hP π Q hBC v w i ⟨hi.cont, hi.loc⟩ B⟩
  · have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    refine (hw ((l : ℕ) : 𝓞 K)).1 ?_
    simpa using h1
  · rw [← GlobalTheory.LiftAbsPow.absNorm_eq_normV, ← GlobalTheory.LiftAbsPow.absNorm_eq i hi.cont]
    exact absNorm_rat Fact.out v hlv
  · intro g hg x
    apply Bw.j.injective
    have := Bw.e_comm ⟨g, hg⟩ (algebraMap K Ω x)
    rw [← this]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e ⟨g, hg⟩).2 _ (hjK x)
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TConjK
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull
namespace UpperTheory.V.Af
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩
end UpperTheory.V.Af
open UpperTheory.V.Af in
theorem UpperTheory.V.Af.conjK_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.ConjK := by
  intro P K _ _ _ n hn m hm M hM σ π ⟨hinf, hdual, hfix⟩
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π (regAlg_of_infOf hm hinf) σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hfix' := hs.hasFixed hfix
  refine ⟨π', ⟨fun φ => ?_, ?_, hfix'⟩, fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  · obtain ⟨ht, ht'⟩ := sep_theta (GlobalTheory.CsdBack.isCsd_of_paired P.litN.aut.fin K n π (P.litN.aut.gk K n π) hdual) hs hs'
    refine GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (P.litN.aut.gk K n π') (isCsd_of_iso (Quotient.exact
      (P.litN.aut.js.1.strong_multiplicity_one (by omega) (CG.mk (thetaSub π')) (CG.mk π') ?_)))
    refine (eventually_notMem hM).mono fun w hw => ?_
    obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π' hfix' w hw
    exact ⟨B, (ht.comp _).hasSatGL_refl (ht'.comp _) hB, hB⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open IsDedekindDomain UpperTheory.V.Af in
theorem UpperTheory.GalN.V.csdOf0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω]
    [Algebra F Ω] [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], IsTotallyReal F₀ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c → IsAut ι r →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ))) P → AutCsd0 ι r := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := _root_.UpperTheory.V.Af.self_dual_complex_of_printed_hida hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end
end

