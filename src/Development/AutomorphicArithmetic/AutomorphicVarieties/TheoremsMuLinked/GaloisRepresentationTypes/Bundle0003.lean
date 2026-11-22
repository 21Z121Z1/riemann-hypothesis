import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CornerStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.Temper
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
import Formalism.PrimeAboveExistence.LenEqPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RigPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ReducibleThreeDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanCocIsBK
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdLAbove
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem adL_conj {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (γ g : G) :
    c g = ρ γ (c (γ⁻¹ * g * γ)) + c γ - ρ g (c γ) := by
  have h1 := hc γ (γ⁻¹ * g * γ)
  rw [← mul_assoc, mul_inv_cancel_left, hc] at h1
  rw [eq_sub_iff_add_eq, h1, add_comm]

private theorem adL_rho {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (γ g : G) (x : V) : ρ γ (ρ (γ⁻¹ * g * γ) x) = ρ g (ρ γ x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply]

private theorem adL_emb {F Ω K : Type} [Field F] [Field Ω] [Field K] [CharZero F] [Algebra F Ω] [IsAlgClosure F Ω]
    (j j₀ : Ω →+* K) (h : j₀.comp (algebraMap F Ω) = j.comp (algebraMap F Ω)) :
    ∃ γ : Ω ≃ₐ[F] Ω, ∀ y, j (γ y) = j₀ y := by
  letI : Algebra F K := (j.comp (algebraMap F Ω)).toAlgebra
  letI : Algebra Ω K := j.toAlgebra
  haveI : IsScalarTower F Ω K := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ω →ₐ[F] K := { j₀ with commutes' := fun x => RingHom.congr_fun h x }
  exact ⟨f.restrictNormal' Ω, fun y => f.restrictNormal_commutes Ω y⟩

private theorem adL_above {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (j : Ω →+* Formalism.BasicNotions.Loc.Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* Formalism.BasicNotions.Loc.GQ l) (ψ : H →* G F Ω) (hφ : Topology.IsOpenEmbedding φ) (hψ : Continuous ψ)
    (hj : ∀ h y, φ h (j y) = j (ψ h y))
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) : (fun h => c (ψ h)) ∈ Loc.finiteCocycles φ (ρ.comp ψ) := by
  obtain ⟨j₀, hj₀, h0⟩ := hb.above (j.comp (algebraMap F Ω))
  obtain ⟨γ, hγ⟩ := adL_emb j j₀ hj₀
  let ψ' : H →* G F Ω := (MulAut.conj (γ⁻¹ : G F Ω)).toMonoidHom.comp ψ
  have hψ' : ∀ h, ψ' h = γ⁻¹ * ψ h * γ := fun h => by simp [ψ']
  obtain ⟨-, x, hx⟩ := (Loc.bkAbove (F := F) j₀ φ ψ' hφ (fun h y => by
    rw [← hγ, hj, ← hγ, hψ']
    simp) ρ c hc).2 h0
  refine ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩,
    TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id x - c γ ⊗ₜ[ℚ_[l]] 1, fun h => ?_⟩
  have e : ∀ w, TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id (Loc.actC φ (ρ.comp ψ') h w) =
      Loc.actC φ (ρ.comp ψ) h (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [Loc.actC, TensorProduct.AlgebraTensorModule.map_tmul, MonoidHom.comp_apply, hψ', adL_rho, LinearMap.id_apply]
    | add u v hu hv => simp only [map_add, hu, hv]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id) (hx h)
  rw [map_sub, e, TensorProduct.AlgebraTensorModule.map_tmul] at h2
  have h3 : Loc.actC φ (ρ.comp ψ) h (c γ ⊗ₜ[ℚ_[l]] 1) = ρ (ψ h) (c γ) ⊗ₜ[ℚ_[l]] 1 := by simp [Loc.actC]
  change c (ψ h) ⊗ₜ[ℚ_[l]] _ = _
  rw [adL_conj ρ c hc.2 γ (ψ h), TensorProduct.sub_tmul, TensorProduct.add_tmul, map_sub, h3]
  simp only [LinearMap.id_apply, hψ'] at h2
  rw [h2]
  abel

open scoped Pointwise in
private theorem adL_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} (γ : G F Ω)
    {g : G F Ω} (hg : g ∈ Ine (F := F) (γ • A)) : γ⁻¹ * g * γ ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, γ y ∈ γ • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff (g := γ)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : g • γ • A = γ • A := hg.1
    change (γ⁻¹ * g * γ) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h2 := hg.2 (γ x) (by rwa [ValuationSubring.valuation_le_one_iff, m, ← ValuationSubring.valuation_le_one_iff])
    have e : g (γ x) - γ x = γ ((γ⁻¹ * g * γ) x - x) := by simp
    rwa [e, valuation_lt_one_iff', m, ← map_inv₀, m, map_eq_zero_iff _ γ.injective, ← valuation_lt_one_iff'] at h2

private theorem adL_away {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A w) : ∃ x : V, ∀ g ∈ Ine (F := F) A, c g = ρ g x - x := by
  obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w hw
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
  refine ⟨ρ γ x - c γ, fun g hg => ?_⟩
  rw [adL_conj ρ c hc.2 γ g, hx _ (adL_ine γ hg), map_sub, adL_rho, map_sub]
  abel

private theorem adL_pr {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

private theorem adL_desc {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : G →* GL (Fin n) A) (hD : D.comap φ = W.GDet.ofRep (W.mat (ρ.comp φ))) :
    D = W.GDet.ofRep (W.mat ρ) := by
  refine CA.d_gext _ _ fun g i _ _ => ?_
  obtain ⟨h, rfl⟩ := hφ g
  have e : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
    change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
    congr 1
    rw [map_sub]
    simp
  unfold W.GDet.lam
  rw [← e, hD, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1]
  rfl

private theorem adL_triv {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    {ι : Qbar l ≃+* ℂ} {x : B.Pt} {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (H : NiceAPt ι x ρ) :
    ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 :=
  (Ws.Eb.relKill B x ρ ((AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => H.irr N fun g _ v hv => hN g v hv)
    (adL_desc x.D V.pr (adL_pr V) ρ H.rep)).2

theorem UpperTheory.V.Th.adL_of :
    Loc.LocalPublishedTheorems → Core → AdL := by
  intro hP hC l _ L Ω _ _ _ _ _ _ s V hS hζ c hL n hn hn' r hr B ι x ρ H hpar P R hform hR z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hz' : (fun g => z (toGS Ω V.S' g)) ∈ Z1 (R.comp (toGS Ω V.S') :
      Representation (Qbar l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (Qbar l))) :=
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩
  have he : V.frame.eps c.O (Qbar l) = V.frame.eps ℤ_[l] (Qbar l) := by
    unfold W.GFrame.eps
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine hC l L Ω s V hS hζ c hL n hn hn' r hr B ι x ρ H P R (fun g => he ▸ hform g) hR z hz ⟨fun u g hg => ?_, fun v => ?_⟩
  · obtain ⟨X, hX⟩ := adL_away _ _ hz' hb u.1 (s.St_l u.1 u.2) (s.A u.1) (s.hA u.1)
    have h1 := adL_triv H u g hg
    obtain ⟨g', hg', rfl⟩ := hg.1
    have h2 := hX (W.resP L Ω g') hg'
    have h3 : ∀ g : V.frame.G₀, ρ g = 1 → Loc.adGL ρ g X = X := fun g h => by simp [Loc.adGL, h]
    exact h2.trans (sub_eq_zero.2 ((hR.ad (V.pr g') X).trans (h3 _ h1)))
  · obtain ⟨j, hj⟩ := (Loc.decEmb (F := W.Lp L) (Ω := Ω) (v := l)).1 (s.A v.1) v.1 (s.hA v.1) v.2
    have key : ∃ φ : ↥(Dec (F := L) (s.A v.1)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
        (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A v.1)) ∧
        (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
      rw [← hj]
      obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
      exact ⟨φ, a, b, c, d l⟩
    obtain ⟨φ, a, b, hi, d⟩ := key
    have d' : ∀ g, Loc.cycA l l (Qbar l) (φ g) = cycBar L Ω l (g : G L Ω) := fun g => congrArg (Units.map _) (d g)
    have h3 := adL_above (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) a
      (W.continuous_resP.comp continuous_subtype_val) b _ _ hz' hb
    have e : ((R.comp (toGS Ω V.S')).comp ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) :
        Representation (Qbar l) (Dec (F := L) (s.A v.1)) (Matrix (Fin n) (Fin n) (Qbar l))) =
        Loc.adGL (ρ.comp (V.frame.φ v)) :=
      MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad (V.frame.φ v g) X
    rw [e] at h3
    obtain ⟨m, k, hm, hk, hψ⟩ := hpar v
    obtain ⟨g₀, hg₀, hf⟩ := H.free v
    have hI : V.frame.Iv v = (Loc.Iq l).comap φ := Subgroup.ext fun g => (hi g).symm
    rw [hI]
    haveI : CompactSpace (Dec (F := L) (s.A v.1)) := V.frame.cv v
    refine bkOrd hP l (Dec (F := L) (s.A v.1)) φ a n _ _ m k (H.cont.comp (V.frame.φ_cont v)) (H.flag v) hm hk
      (fun i i' g hg => ?_) ⟨g₀, ?_, hf⟩ _ h3
    · rw [d']
      exact hψ i i' g ((hi g).1 hg)
    · have h4 : cycZ (W.Lp L) Ω l (W.resP L Ω g₀.1) = 1 := by
        rw [← V.hε]
        exact hg₀
      have h5 : Loc.cyc l l (φ g₀) = 1 := (d g₀).trans h4
      exact (congrArg (Units.map _) h5).trans (map_one _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreeFlagO
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Th.freeFlagO :
    Af.HypothesesH → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → Af.IsAutCsd ι r →
        ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ),
          W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k →
          (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) →
          ((∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ (Odd n ∧ Af.PotCrysAt r A)) →
          ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n hn r hr ⟨π, hreg, hcsd, hatt⟩ A hA ψ m k hflag hm hk hine hgen
  have P := PH.toClassicalTheorems
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar F ^ n) :=
    ⟨fun v => by
      have e : (quadChar F ^ n).locInf v (-1) = (quadChar F).locInf v (-1) ^ n := rfl
      rw [e, quadChar_locInf],
     by rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hcsd⟩
  obtain ⟨w, h, hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).2 hA
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P F n π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  have hc := (compatCsd PH F Ω l ι n hn r π hr hreg hcsd hatt w σ hσ A h rc hrc).2
  exact purLocS P F Ω l hl ι n r hr w A h hw (rc (algNorm σ))
    (fun O _ _ _ Bw hj => ⟨(hc O Bw hj).1, by first | exact Lev.SsCmp.of_eq (hc O Bw hj).2 | exact (hc O Bw hj).2⟩)
    (temper P F Ω n hn π hreg ⟨_, hpol⟩ w A h rc hrc σ hσ) ψ m k hflag hm hk hine
    (hgen.imp_right fun hp =>
      Lev.monoOdd P F n hp.1 l Ω ι r π hr hreg hcsd hatt w A h hp.2 σ hσ rc hrc)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreePU
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hA : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom).tower_top : IsIntegral A (algebraMap F Ω (x : F)))
    exact hy ▸ y.2
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hA
  have hf : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hm : (p : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f := (hf _).1 (by simpa using hp)
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, hf, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hp0 (Nat.cast_eq_zero.1 hm)

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  let S : SubMulAction (G F Ω) Ω :=
    { carrier := {ζ | ζ ^ M = 1}
      smul_mem' := fun s ζ (h : ζ ^ M = 1) => by
        show (s ζ) ^ M = 1
        rw [← map_pow, h, map_one] }
  haveI : Finite S := by
    classical
    refine Set.Finite.subset (s := ((nthRoots M (1 : Ω)).toFinset : Set Ω)) (Finset.finite_toSet _) fun ζ h => ?_
    exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((mem_nthRoots hM).2 h))
  refine ⟨Nat.card (Equiv.Perm S), Nat.card_pos, fun C _ χ h s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  have e : MulAction.toPermHom (G F Ω) S (s ^ Nat.card (Equiv.Perm S)) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg Subtype.val (DFunLike.congr_fun e ⟨ζ, hζ⟩)

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨a, ha⟩ := h
  have h1 := Matrix.charpoly_of_upperTriangular ((a * r s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    fun i j hij => (ha s).1 i j hij
  simp only [(ha s).2] at h1
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem UpperTheory.V.Th.freePU :
    Af.HypothesesH → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Continuous r → AutP ι r → Unl l M m r → FreeAt l r := by
  intro PH K Ω _ _ _ _ _ _ hK l _ hl ι n hn r M m hM hm hr haut hU B hB
  have P : Af.Hypotheses₂ := PH.toClassicalTheorems
  obtain ⟨w, hBw, hw⟩ := place_under (F := K) (Fact.out : l.Prime).ne_zero hB
  obtain ⟨π, hreg, hpol, hatt⟩ := haut
  obtain ⟨A, hA, κ, hF, hunl⟩ := hU w hw
  obtain ⟨χ, hχ, hflag, hκ⟩ := id hF
  obtain ⟨rc, hrc⟩ := P.exists_rec hA
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P K n π w
  obtain ⟨k, hk, hpow⟩ := pow_eq_one_of_kills (F := K) (Ω := Ω) hM
  have hflag' : W.HasFlag (r.comp (Dec (F := K) A).subtype) κ := hflag
  obtain ⟨g, hg, hfree⟩ := purLocS P K Ω l hl ι n r hr w A hA hw (rc (algNorm σ))
    (fun O _ _ _ Bw hj => by
      obtain ⟨h1, h2⟩ := Lev.compatPSOf P P.ss K hK n hn l Ω ι r π hr hreg hpol hatt
        w A hA O Bw hj
      obtain ⟨μ, hμ, -⟩ := Lev.flagPol K Ω l ι n M hM m r hr w A hA O Bw hj κ hF h1
      exact ⟨h1, fun _ => h2 σ hσ rc hrc ⟨μ, hμ⟩⟩)
    (temper P K Ω n (by omega) π hreg hpol w A hA rc hrc σ hσ) κ m k hflag' hm hk
    (fun i s hs => by
      rw [hκ i s hs, zpow_neg, mul_inv_cancel_comm]
      exact hpow _ _ (hχ i) _) (Or.inl hunl)
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := K) hA hBw
  refine ⟨t * g * t⁻¹, ?_, ?_, fun i => κ i g, hfree, ?_⟩
  · have h1 : (g : G K Ω) • A = A := g.2
    show (t * (g : G K Ω) * t⁻¹) • t • A = t • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, hg]
  · have h1 := charpoly_of_flag hflag' g (r t)
    rw [← h1]
    show (r (t * g * t⁻¹)).val.charpoly = _
    rw [map_mul, map_mul, map_inv]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LinkedRig
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

theorem UpperTheory.V.Th.linkedRig :
    Af.HypothesesH → AdL → LinkedRig := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed
  have hP : Af.Hypotheses₂ := hH.toClassicalTheorems
  have hN := hP.litN
  have hA : GlobalTheory.Published.GlobalArtinReciprocity := hN.aut.art
  have hC : Pa.CohP :=
    ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hLoc : W.LocCFTAll := W.locCFT hA hC
  have hB0 : W.ProModularRingExists := W.b0Ex (W.phiAll hC)
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hker : η.ker = Base.galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := Sd.twist hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := Pr.kaOf (Sd.algCyc hP) (Sd.algRes hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, -⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := Pr.coefIs l c₁
  obtain ⟨R₂⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  exact ⟨rigPtOf hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3,
    ka, hk2, rigPtOf hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapReducibleThreeDim
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have hk : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have key := normO l c.O b h0
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hk
  by_contra hge
  push_neg at hge
  have h1 := one_le_pow₀ (n := (eO l c.O).toNat) hge
  linarith

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  have hsurj : Function.Surjective x := fun a => ⟨algebraMap c.O R a, x.commutes a⟩
  have hmax : (Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hsurj
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hy' : y ∈ Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O) := heq ▸ hy
  have hxy : x y ∈ IsLocalRing.maximalIdeal c.O := hy'
  exact norm_lt_one_of_nonunit c (x y) ((IsLocalRing.mem_maximalIdeal _).mp hxy)

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  apply SemidirectProduct.ext
  · apply Units.ext
    ext i j
    simp only [MonoidHom.comp_apply, GG.map, r0, MonoidHom.coe_mk, OneHom.coe_mk,
      SemidirectProduct.map_left, GeneralLinearGroup.map_apply, tor_val, RingHom.mapMatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) (Ψ g) (wt1 i))
    · simp [Matrix.diagonal_apply_ne _ hij]
  · simp [GG.map, r0]

private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG 3 κ)
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨X, hX⟩ := LinearMap.mem_range.mp h
  refine ⟨-X, ?_⟩
  funext g
  rw [← hX]
  show adRep r g X - X = -X - adRep r g (-X)
  rw [map_neg]
  abel

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) := by
  intro g
  refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
  unfold entAlg
  exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩

theorem UpperTheory.V.Th.ptHyp_of :
    Th.InpU → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), Aut.AutB D ι g₁ → Aut.LemW D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]
    rfl
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hI.toCohInp D hM (isPt_push D hM S f hf) hU hL
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ isLocPt_toBar x₀)
    rw [hF, h0] at h1
    rw [h0]
    exact coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hI.toCohInp D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hI.rigI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult (isPush_push f _) h)
      · exact Th.blochKatoSelmer_adRep_vanishes_of_typeII_modular hI D hM S f hf.1 ι h
          (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1)
    exact coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)
end

