import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.TwistOfRed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorOfLocalFixedVectors
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_of_local_fixed_vectors :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ K : Subgroup (UA E n), K ≤ finU E n → (∀ w, ∀ k ∈ K, GlobalTheory.DefU.LocRet.ret0 w n k ∈ K) → ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite → (∀ k ∈ K, ∀ u ∉ T, cLoc u k ∈ GlobalTheory.LFun.KGL u n) → (∀ w, ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU E n k φ = φ) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  classical
  intro E _ _ _ n σ hσ K hKf hKr T hT hKT h
  let P : Finset (HeightOneSpectrum (𝓞 E)) → UA E n → Prop := fun S k =>
    k ∈ K ∧ ∀ w ∈ S, ∀ u : HeightOneSpectrum (𝓞 E),
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u k = 1
  have hR : ∀ (a b : UA E n) (φ : UA E n → ℂ), RU E n (a * b) φ = RU E n a (RU E n b φ) := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P S k → RU E n k φ = φ) →
      ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P ∅ k → RU E n k φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hvσ, hv0, hv⟩
      let W : Submodule ℂ (UA E n → ℂ) := σ ⊓ ⨅ k : {k // P (insert w S) k}, LinearMap.ker (RU E n k.1 - 1)
      have hWm : ∀ x, x ∈ W ↔ x ∈ σ ∧ ∀ k, P (insert w S) k → RU E n k x = x := fun x => by
        simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero, Subtype.forall]
      obtain ⟨φ, hφ, hφ0, hφK⟩ := h w
      obtain ⟨x, hxW, hx0, hx⟩ := UpperTheory.exists_fixed_vector_in_locally_stable_subspace E n σ hσ w (K ⊓ locU n w) inf_le_right
        ⟨φ, hφ, hφ0, fun k hk => hφK k hk.1 hk.2⟩ W inf_le_left
        (fun e => hv0 (by
          have := (hWm v).2 ⟨hvσ, hv⟩
          rwa [e, Submodule.mem_bot] at this))
        (fun g hg x hx => (hWm _).2 ⟨hσ.stable g x ((hWm x).1 hx).1, fun k hk => by
          have e : k * g = g * k := by
            refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
            · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hg, one_mul, mul_one]
            · by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
              · have h1 : Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) k.1 = 1 :=
                  hk.2 w (Finset.mem_insert_self _ _) u hu
                simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
              · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hg hu, one_mul, mul_one]
          rw [← hR, e, hR, ((hWm x).1 hx).2 k hk]⟩)
      refine ih ⟨x, ((hWm x).1 hxW).1, hx0, fun k hk => ?_⟩
      have h1 : GlobalTheory.DefU.LocRet.ret0 w n k ∈ K := hKr w k hk.1
      have h2 : P (insert w S) (k * (GlobalTheory.DefU.LocRet.ret0 w n k)⁻¹) := by
        refine ⟨mul_mem hk.1 (inv_mem h1), fun w' hw' u hu => ?_⟩
        by_cases huw : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = cLoc u k := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq huw k
          rw [map_mul, map_inv, h3, mul_inv_cancel]
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = 1 := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne huw k
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact absurd hu huw
          · rw [map_mul, map_inv, h3, hk.2 w' hw' u hu, inv_one, mul_one]
      have h3 : RU E n (GlobalTheory.DefU.LocRet.ret0 w n k) x = x := hx _ ⟨h1, GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k⟩
      have h4 := ((hWm x).1 hxW).2 _ h2
      rwa [← h3, ← hR, inv_mul_cancel_right, h3] at h4
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff σ).1 hσ.ne_bot
  obtain ⟨S, hS⟩ := UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places E n T hT _ ((hσ.aut v hv).level.mem_nhds (x := 1) (by simp))
  obtain ⟨x, hx, hx0, hxK⟩ := key S ⟨v, hv, hv0, fun k hk =>
    hS ⟨k, hKf hk.1⟩ (hKT k hk.1) fun u hu => hk.2 u hu u rfl⟩
  exact ⟨x, hx, hx0, fun k hk => hxK k ⟨hk, by simp⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.finiteSum_reduction :
    SumRed := by
  intro Γ k _ _ a b r r' ha hb hirr
  let W : Submodule k (Fin (a + b) → k) :=
    { carrier := {v | ∀ j : Fin b, v (Fin.natAdd a j) = 0}
      add_mem' := by
        intro x y hx hy j
        simp [hx j, hy j]
      zero_mem' := by
        intro j
        rfl
      smul_mem' := by
        intro c x hx j
        simp [hx j] }
  have hinv : Formalism.MainNotions.N.IsInv (Formalism.MainNotions.SumRepresentations.At.sumRep r r') W := by
    intro g v hv j
    have hM : ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a+b)) k) : Matrix (Fin (a+b)) (Fin (a+b)) k) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (((r g) : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) (0 : Matrix (Fin a) (Fin b) k)
            (0 : Matrix (Fin b) (Fin a) k) (((r' g) : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) := rfl
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    simp [hv _]
  have hne : W ≠ ⊥ := by
    intro h
    have hmem : (Pi.single (Fin.castAdd b ⟨0, ha⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      intro j
      rw [Pi.single_apply, if_neg]
      intro h'
      exact absurd h' (Fin.ne_of_val_ne (by simp; omega))
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem (Fin.castAdd b ⟨0, ha⟩)
    simp at this
  have hntop : W ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (Fin.natAdd a ⟨0, hb⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      rw [h]
      exact Submodule.mem_top
    have := hmem ⟨0, hb⟩
    simp at this
  rcases hirr.2.2 W le_top hinv with h | h
  · exact hne h
  · exact hntop h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusConjOfGaloisConjugatePlaces
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
open scoped Pointwise

private theorem normV_pre {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conj {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem exists_pre {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (w w' : HeightOneSpectrum (𝓞 M)) (h : w'.under (𝓞 K) = w.under (𝓞 K)) :
    ∃ g : M ≃ₐ[K] M, preplace g.toRingEquiv w' = w := by
  have h' : w'.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  have := w.isPrime
  have := w'.isPrime
  have : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨rfl⟩
  have : w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨h'.symm⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (M ≃ₐ[K] M)
  refine ⟨g, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [mem_preplace, ← hg]
  exact Ideal.smul_mem_pointwise_smul_iff (a := g) (x := x)

theorem UpperTheory.frobenius_conj_of_galois_conjugate_places :
    UpperTheory.V.Af.Sol.FrobConj := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r w w' h
  obtain ⟨g, rfl⟩ := exists_pre w w' h
  refine ⟨(normV_pre _ _).symm, fun B hB A' hA' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) g.toRingEquiv
  let s : G K Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, hσ]
    exact congrArg (algebraMap M Ω) (g.commutes x)
  have key : ∀ t : G M Ω, r (resG K M Ω t) = r s * r (resG K M Ω (conjGal hσ t)) * (r s)⁻¹ := fun t => by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => (apply_conjGal hσ t x).symm
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun _ => Iff.rfl
  obtain ⟨h1, h2⟩ := hB _ (isPlaceOver_preplace hσ hA hA')
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have e : r (resG K M Ω (conjGal hσ t)) = 1 := h1 _ (conjGal_mem_Ine hσ hA ht)
    rw [MonoidHom.comp_apply, key, e, mul_one, mul_inv_cancel]
  · have e := h2 (conjGal hσ t) (by rw [normV_pre]; exact isFrob_conj hσ hA ht)
    rw [← e, ← map_inv (conjGal hσ), MonoidHom.comp_apply, MonoidHom.comp_apply, key t⁻¹,
      Units.val_mul, Units.val_mul, Matrix.coe_units_inv (r s), Matrix.charpoly_units_conj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterOfAlgebraicHecke
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_rank_one_rep {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
  ext g
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

private theorem tw_eq {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l)) (μ : Γ →* (Qbar l)ˣ) :
    Af.tw R μ = Formalism.MainNotions.SumRepresentations.At.twGL R (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
  rw [det_rank_one_rep]
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

private theorem tw_comp {Γ Γ' : Type} [Group Γ] [Group Γ'] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l))
    (μ : Γ →* (Qbar l)ˣ) (f : Γ' →* Γ) :
    (Af.tw R μ).comp f = Formalism.MainNotions.SumRepresentations.At.twGL (R.comp f) (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp f)) := by
  rw [tw_eq]; rfl

private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this

theorem UpperTheory.galois_character_of_algebraic_hecke :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R → (∃ HT, Af.HasHT R HT) → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsAlgPos κ m → Continuous μ → IsLAdicOf art ι κ m μ → (∃ HT, Af.HasHT (Af.tw R μ) HT) ∧ ∀ (w : Plc K) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))), Af.LocGlob ι R w τ → Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Af.LocGlob ι (Af.tw R μ) w τ' := by
  intro P K Ω _ _ _ _ _ _ l _ ι n R hR hHT art κ m μ hart hκ hμ hL
  obtain ⟨HT, hHT⟩ := hHT
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have H1 : Af.HasHT (Af.tw R μ) fun τ => (HT τ).map (· + -m (ι.toRingHom.comp τ)) := by
    intro w A h O _ _ _ Bw hj
    obtain ⟨d1, j1⟩ := hHT w A h O Bw hj
    obtain ⟨d2, -, -, j2⟩ :=
      GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj
    have t := GlobalTheory.TwistAbove.twist_above l _ _ ⟨T⟩ K Ω _ O Bw n (R.comp (Dec (F := K) A).subtype)
      ((Af.tw R μ).comp (Dec (F := K) A).subtype) (μ.comp (Dec (F := K) A).subtype) fun g => Af.tw_val R μ g.1
    exact ⟨t.1 d1 d2, fun τ L' τ' hτ => t.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ)⟩
  refine ⟨⟨_, H1⟩, fun w τ τ' hτ he A h rc hrc => ?_⟩
  obtain ⟨h1, h2⟩ := hτ A h rc hrc
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have e : rc (algNorm τ') = (rc (algNorm τ)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [rec_algNorm hrc, rec_algNorm hrc, GlobalTheory.NuShift.lpChar_lpTw]
    obtain ⟨a, ha, ε, -, HL⟩ := hrc
    rw [← HL.twist, GlobalTheory.LocGL.IrrGL.tw_of]
    exact congrArg (fun x => (rc x).lpTw _) (IrrGL.of_eq_of.2 he)
  rw [e]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hc.1]
  have hcR := Units.continuous_val.comp hR
  have hct : Continuous fun g => ((Af.tw R μ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    simp only [Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul hcR
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩
  · have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
      fun g => rfl
    have h3 := isWDOf_wdOf (h := h) (r := Af.tw R μ) hw ι hct
    have h4 := wdOf_twGL_det K Ω A w h l hw ι n R _ hcR (continuous_rank_one_rep hμ)
    rw [← tw_eq, (h1 hw).wdOf_eq hw,
      wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (κ.loc w).comp a) fun _ => ha.smooth hc.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h4
    rw [h4] at h3
    exact h3
  · obtain ⟨p1, w1⟩ := h2 O Bw hj
    have p3 := P.aut.berger.isPstAt T Bw _ (hct.comp continuous_subtype_val) (H1 w A h O Bw hj).1
    have c2 := (continuous_rank_one_rep hμ).comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A))
    have p2 := P.aut.berger.isPstAt T Bw ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype) c2
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj).1
    refine ⟨p3, ?_⟩
    have htw : (Af.tw R μ).comp (Dec (F := K) A).subtype =
        Formalism.MainNotions.SumRepresentations.At.twGL (R.comp (Dec (F := K) A).subtype)
          (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)) := by
      exact tw_comp R μ _
    rw [htw] at p3 ⊢
    rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι K Ω A w h O Bw hj n _ _ (hcR.comp continuous_subtype_val) c2 p1 p2 p3,
      P.aut.chW K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj _ hc a ha]
    refine ((UpperTheory.V.Lev.ssCalc K Ω A w h).2.2 _ _ _ ?_).2 w1
    rw [← HL.one _ hc.1]
    exact HL.dim _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.SumParam

theorem UpperTheory.galoisRep_direct_sum_away_from_places :
    SumAway := by
  intro E Ω _ _ _ _ _ l _ ι a b r r' hr hr' w hl A h x x' hx hx'
  have c : Continuous fun g => ((r g : GL (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin a) (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have c' : Continuous fun g => ((r' g : GL (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin b) (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr'
  have cs : Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin (a + b)) (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) := by
    simp only [coe_sumRep]
    exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _
  rw [← hx.wdOf_eq hl, ← hx'.wdOf_eq hl, ← wdOf_sumRep hl ι r r' c c']
  exact isWDOf_wdOf hl ι cs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationImageSpec
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_representation_image_spec :
    UpperTheory.V.Af.Sol.GalRange := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  let ρ : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hker : (resG K M Ω).range = ρ.ker := by
    ext σ
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨τ, rfl⟩
      ext x
      apply (algebraMap M Ω).injective
      rw [show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp [resG]
    · intro h
      have hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x := by
        intro x
        have := AlgEquiv.restrictNormal_commutes σ M x
        rw [show σ.restrictNormal M = ρ σ from rfl, h] at this
        simpa using this.symm
      refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
      ext x
      rfl
  refine ⟨hker ▸ ρ.normal_ker, ?_⟩
  rw [hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationIrreduciblePrimeDimension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private noncomputable def linRep {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    Representation k Γ (Fin n → k) where
  toFun g := Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem linRep_apply {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    linRep r g v = (r g : Matrix (Fin n) (Fin n) k).mulVec v := rfl

private theorem isIrr_iff {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    IsIrr r ↔ (linRep r).IsIrreducible := by
  constructor
  · rintro ⟨h0, -, h⟩
    haveI : Nontrivial (Subrepresentation (linRep r)) := ⟨⊤, ⊥, fun h' =>
      h0 (congrArg Subrepresentation.toSubmodule h')⟩
    refine ⟨fun S => ?_⟩
    rcases h S.toSubmodule le_top (fun g v hv => S.apply_mem_toSubmodule g hv) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1
  · intro h
    refine ⟨fun h0 => ?_, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    · exact bot_ne_top (α := Subrepresentation (linRep r)) (Subrepresentation.toSubmodule_injective h0.symm)
    · rcases h.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (linRep r)) with h1 | h1
      · left; exact congrArg Subrepresentation.toSubmodule h1
      · right; exact congrArg Subrepresentation.toSubmodule h1

private theorem isIrr_comp_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (φ : Γ' →* Γ) (h : IsIrr (r.comp φ.range.subtype)) : IsIrr (r.comp φ) := by
  obtain ⟨h0, -, h⟩ := h
  refine ⟨h0, fun _ _ _ => Submodule.mem_top, fun W hle hW => h W hle ?_⟩
  rintro ⟨_, g, rfl⟩ v hv
  exact hW g v hv

theorem UpperTheory.galois_representation_irreducible_prime_dimension :
    UpperTheory.V.Af.Sol.IrrPrime := by
  intro Γ Γ' k _ _ _ _ _ n r φ hN hp hn hr
  apply isIrr_comp_of_range
  rw [isIrr_iff]
  by_contra hred
  haveI : φ.range.FiniteIndex := ⟨hp.ne_zero⟩
  have hcomm : commutator Γ ≤ φ.range := by
    haveI : Fact (φ.range.index).Prime := ⟨hp⟩
    haveI : IsCyclic (Γ ⧸ φ.range) := isCyclic_of_prime_card (p := φ.range.index) rfl
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    letI := IsCyclic.commGroup (α := Γ ⧸ φ.range)
    exact mul_comm _ _
  obtain ⟨η, hη, hker, e, he⟩ := UpperTheory.V.AlgebraTools.twistOfRed k Γ (Fin n → k) (linRep r) φ.range
    (Nat.cast_ne_zero.mpr hp.ne_zero) hcomm ((isIrr_iff r).mp hr) hred
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hr.1 (Subsingleton.elim _ _)
  apply hη
  ext g
  have h1 : η g ^ φ.range.index = 1 := by
    rw [← map_pow]; exact hker (Subgroup.pow_index_mem _ g)
  have h2 : η g ^ n = 1 := by
    have hl : linRep r g ∘ₗ (e : (Fin n → k) →ₗ[k] (Fin n → k)) =
        (η g : k) • ((e : (Fin n → k) →ₗ[k] (Fin n → k)) ∘ₗ linRep r g) := LinearMap.ext fun v => he g v
    have hd := congrArg LinearMap.det hl
    rw [LinearMap.det_smul, LinearMap.det_comp, LinearMap.det_comp, Module.finrank_fin_fun] at hd
    have hu : IsUnit (LinearMap.det (linRep r g)) := ((Group.isUnit g).map (linRep r)).map LinearMap.det
    have hue : IsUnit (LinearMap.det (e : (Fin n → k) →ₗ[k] (Fin n → k))) := e.isUnit_det'
    have hne := mul_ne_zero hue.ne_zero hu.ne_zero
    apply Units.ext
    apply mul_right_cancel₀ hne
    rw [Units.val_pow_eq_pow_val, ← hd, Units.val_one, one_mul, mul_comm]
  have hc : Nat.Coprime φ.range.index n := Nat.coprime_of_lt_prime hn0 hn hp
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hc, pow_one] at this
  simp [this]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.half_of_compatible_polarization :
    HypothesesH → Eta → TwistLoc → CompatPol → Half := by
  intro H hEta hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  obtain ⟨ξ, mξ, hξ, hN⟩ := hEta E (e + a - 1)
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  have hd : GlobalTheory.ContraPair.DualIsConj ((P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).twist ξ) := by
    rw [← CuspSub.twist_mul]
    exact Cq.csdTwist E a P 1 _ ((GlobalTheory.ContraPair.dualIsConjBy_one P).2
      (GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (H.litN.aut.gk E a P) hP)) (by rw [hN, inv_one])
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ ξ mξ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) hξ hd σ hσ
  refine ⟨r, HT, ⟨hr.cont, hr.ss, hr.ht, fun w => (hr.par w).congr fun A h rc hrc => ?_⟩, fun τ => ?_⟩
  · obtain ⟨_, _, _, -, L⟩ := hrc
    rw [← L.nu_eq]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.hasWeightAt_of_tensor_dual_intertwiner :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (φ : I → E →+* ℂ), (Function.Injective fun i => InfinitePlace.mk (φ i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)) (Φ : Module.Dual ℂ (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (UA E n → ℂ)), Φ ≠ 0 → (∀ ℓ, Φ ℓ ∈ σ) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x⁻¹))) → ∀ i, HasWeightAt σ (φ i) (lam i).dual := by
  intro E _ _ _ n hn I _ φ hφ lam σ Φ hΦ hσ heq y
  obtain ⟨F, hF0, hF⟩ := UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor I (fun i => nablaSq ℂ n (lam i)) _ Φ hΦ y
  obtain ⟨e, he⟩ := (GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual n hn (lam y)).symm.trans (GlobalTheory.T.iso_unitaryIrrep_conj_dual n (lam y))
  obtain ⟨u, hu⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (φ y)
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n _, (Φ ∘ₗ F) ∘ₗ e.toLinearMap, fun h0 => hF0 ?_, fun v => hσ _, fun x v => ?_⟩
  · apply LinearMap.ext
    intro m
    obtain ⟨v, rfl⟩ := e.surjective m
    exact LinearMap.congr_fun h0 v
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have hT : ∀ i, i ≠ y → GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x.1⁻¹) = LinearMap.id := by
      intro i hi
      have h1 := (Subgroup.mem_inf.1 x.2).2
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 (φ i)
      rw [Subgroup.mem_iInf] at h2
      have h3 : cEmb (φ i) x.1 = 1 := h2 fun h => hi (hφ h)
      rw [map_inv, h3, inv_one, map_one]
      rfl
    change Φ (F (e (GlobalTheory.Branching.sqRep ℂ n (lam y).dual (cEmb (φ y) x.1) v))) = RU E n x.1 (Φ (F (e v)))
    rw [heq _ _ hx, hF _ hT, map_inv, ← hu x]
    congr 2
    rw [← map_inv]
    exact he (u x) v
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.satake_galois_compatibility_of_hecke_eigensystem :
    HypothesesH → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩
end

