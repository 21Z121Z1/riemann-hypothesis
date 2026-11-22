import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
import GroundTheory.GlobalFields.LocalAtPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqInv
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open GlobalTheory.PoleFactor

namespace GlobalTheory.NormFvFacts

theorem absNorm_gt_one (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)

theorem norm_eq_zpow (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
  rfl

theorem norm_le_one_iff (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : Fv F v) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem exists_norm_eq_inv (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  refine ⟨((π : F) : v.adicCompletion F), ?_⟩
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  have key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), Multiplicative.toAdd (WithZero.unzero h) = a := fun a h => rfl
  rw [key, zpow_neg_one]
  rfl

theorem sigmaFinite_haar (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) : SigmaFinite μ := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  have : SecondCountableTopology (Fv F v) := UniformSpace.secondCountable_of_separable (Fv F v)
  have : LocallyCompactSpace (Fv F v) := inferInstance
  infer_instance

end GlobalTheory.NormFvFacts

open GlobalTheory.NormFvFacts in

theorem GlobalTheory.NormFvFacts.main : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), 1 < (Ideal.absNorm v.asIdeal : ℝ) ∧ (∀ x : Fv F v, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k) ∧ (∀ x : Fv F v, ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F) ∧ (∃ ϖ : Fv F v, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) ∧ ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → SigmaFinite μ :=
  fun F _ _ v => ⟨absNorm_gt_one F v, norm_eq_zpow F v, norm_le_one_iff F v, exists_norm_eq_inv F v,
    fun μ hμ => sigmaFinite_haar F v μ hμ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifEnd

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel in

theorem exists_pow_eq_one_of_surjective (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ B.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hgB hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_factor_pow (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A)
    [IsSeparated A'.hom] [LocallyOfFiniteType A'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A ⟶ A') [IsMonHom φ]
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → y ≫ φ = 1) :
    ∃ α : A ⟶ A', IsMonHom α ∧ (𝟙 A ^ N) ≫ α = φ := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨hmon, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have key : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ (𝟙 A ^ N) = 1 → x ≫ φ = 1 := by
    intro T x hx
    let K := pullback (𝟙 A ^ N) η[A]
    let inc : K ⟶ A := pullback.fst ((𝟙 A ^ N)) η[A]
    have hinc : inc ≫ (𝟙 A ^ N) = 1 := by
      rw [pullback.condition, toUnit_unique (pullback.snd ((𝟙 A ^ N)) η[A]) (toUnit K)]; rfl
    have hp := (IsPullback.of_hasPullback ((𝟙 A ^ N)) η[A]).map (Over.forget (Sp ℂ))
    have he : Etale (pullback.snd ((𝟙 A ^ N)) η[A]).left :=
      MorphismProperty.of_isPullback (P := @Etale) hp het
    have hw : (pullback.snd ((𝟙 A ^ N)) η[A]).left = K.hom := by
      simpa using Over.w (pullback.snd ((𝟙 A ^ N)) η[A])
    rw [hw] at he
    have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
    have hk : inc ≫ φ = 1 := by
      refine Over.OverMorphism.ext ?_
      have : LocallyOfFiniteType ((inc ≫ φ).left ≫ A'.hom) := by rw [Over.w]; infer_instance
      refine ext_of_apply_eq A'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
        ((Over.w _).trans (Over.w _).symm)
      let p : Over.mk (𝟙 (Sp ℂ)) ⟶ K :=
        Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
      have hpN : (p ≫ inc) ^ N = 1 := by
        have : (p ≫ inc) ^ N = (p ≫ inc) ≫ (𝟙 A ^ N) := by rw [MonObj.comp_pow, Category.comp_id]
        rw [this, Category.assoc, hinc, MonObj.comp_one]
      have e : p ≫ inc ≫ φ = p ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        exact h _ hpN
      have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
      have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply K.hom z hz _
      simp only [Over.comp_left] at e'
      rw [← hz']
      exact e'
    have hx' : x ≫ (𝟙 A ^ N) = toUnit T ≫ η[A] := hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ φ = 1
    rw [hk, MonObj.comp_one]
  obtain ⟨⟨α, hα, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A A' ((𝟙 A ^ N)) φ hmon
    inferInstance inferInstance hsurj inferInstance key
  exact ⟨α, hα, hc⟩

theorem exists_isMonHom_of_map_lattice :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u.Λ) → ∃ α : A ⟶ A, IsMonHom α ∧ ∀ w, u.ex (M w) = u.ex w ≫ α := by
  intro A _ g hA hgA L u M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', -, hi', hr', hir'⟩ :=
    EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance

  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i

  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0

  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q Q.g v v (J ∘ₗ M ∘ₗ R)
    rfl rfl (fun l hl => hJΛ _ (hM _ (hRΛ _ hl)))
  haveI := hβ
  have hφ : ∀ z, u.ex z ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) = u.ex ((m * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR, hRJ, hRJ, map_nsmul, smul_smul]
  have := hA.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A hA (m * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    ((i ≫ i') ≫ β ≫ (r' ≫ r)) fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m * m ≠ 0 by positivity)
  have hw : (m * m) • (((m * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u.ex (M w) = u.ex ((m * m) • M (((m * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) := (hφ _).symm
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibre

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem unitAt_square (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1 S P (Over.mk t) x₁ x₂
    (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    rw [spec_pt_eq (k := K) q (IsLocalRing.closedPoint K)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem isIntegral_fibre : IsIntegral (Over.mk t ⊗ P.A).left := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  exact GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) t (pullback.snd t P.A.hom)
    (pullback.fst t P.A.hom) (IsPullback.of_hasPullback t P.A.hom).flip

def trY (w : Over.mk t ⟶ P.A) : Over.mk t ⊗ P.A ⟶ Over.mk t ⊗ P.A := lift (fst _ _) (translPt P.A w)

theorem trY_snd (w : Over.mk t ⟶ P.A) :
    (trY P t w).left ≫ (snd (Over.mk t) P.A).left = (translPt P.A w).left := by
  rw [← Over.comp_left, trY, lift_snd]

theorem lift_trY (a w : Over.mk t ⟶ P.A) : lift (𝟙 (Over.mk t)) a ≫ trY P t w = lift (𝟙 (Over.mk t)) (w * a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trY]
  · rw [Category.assoc, trY, lift_snd, lift_snd, translPt, comp_lift_assoc, lift_fst_assoc, Category.id_comp,
      lift_snd, Hom.mul_def]

theorem isUnit_sval_of_mem {X Y Z : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : IsUnit (sval s r z J) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval s r z hJ k hk

theorem exists_sec_twist_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  intro S P K _ _ t c a p
  have hI := isIntegral_fibre P t
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing S P K t hI
  obtain ⟨u, h₁, h₂⟩ := GlobalTheory.T.exists_point_mem_translates' S P K t inferInstance (nonzeroLocus θ) hθ a c p
  obtain ⟨g, hg⟩ := unitAt_square P t (c * u) u⁻¹ ((lift (𝟙 (Over.mk t)) a).left p)
  have hF : FormEq (Sum.elim (Sum.elim (fun k => (trY P t (c * u)).left ≫ ![(snd (Over.mk t) P.A).left] k)
      (fun k => (trY P t u⁻¹).left ≫ ![(snd (Over.mk t) P.A).left] k))
      ![(translPt P.A (c * u * u⁻¹)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A (c * u)).left, (translPt P.A u⁻¹).left])
      (Sum.elim (Sum.elim ![1] ![1]) ![1, 1, -1, -1])
      ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] ![((2 : ℕ) : ℤ) - 1, 1] := by
    refine formEq_of_add fun U _ h => ?_
    simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
    rw [trY_snd, trY_snd, mul_inv_cancel_right]
    simp
    abel
  obtain ⟨σ, hσ⟩ := exists_sec P.isLB hF (mulSec (mulSec (pullSec θ (trY P t (c * u)).left)
    (pullSec θ (trY P t u⁻¹).left)) g)
  refine ⟨σ, ?_⟩
  choose J hJ using fun χ : (Over.mk t ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((lift (𝟙 (Over.mk t)) a).left p))
  have hJ' : Good P.L ((lift (𝟙 (Over.mk t)) a).left p) J := hJ
  refine (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval σ _ hJ').2 ?_
  rw [hσ _ _ _ J hJ', sval_mulSec _ _ _ _ hJ',
    sval_mulSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ']
  refine ((isUnit_sval_of_mem θ _ _ ?_ hJ').mul (isUnit_sval_of_mem θ _ _ ?_ hJ')).mul (hg J hJ')
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₁
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₂

end GlobalTheory.TwistFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.SiegelHt

theorem cone_low {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem form_cols {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (U V : Matrix (Fin n) (Fin q) E) (i j : Fin q) :
    form σ J (fun k => U k i) (fun k => V k j) =
      σ ((Formalism.UG.cT (σ : E →+* E) U * ((1 : E) • J.map σ) * V) i j) := by
  simp only [form, one_smul, Matrix.mul_apply, dotProduct, Matrix.mulVec, map_sum, map_mul, Formalism.UG.cT,
    Matrix.transpose_apply, Matrix.map_apply, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SiegelHt

open GlobalTheory.SiegelHt in
theorem GlobalTheory.SiegelHt.siegel_reduction : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y ∧ ∃ (Cc : Set (UA σ X.J)) (c C : ℝ) (A : ℕ),
      IsCompact Cc ∧ 0 < c ∧ ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J, ∃ (t : Fin q → ℝ) (a κ : UA σ X.J),
        (∀ i, c ≤ t i) ∧ IsTorusU x y t a ∧ κ ∈ Cc ∧ γ * g = a * κ ∧ (ht (a * κ) : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro hP F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : X.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (hX.sig w₀) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]
    refine ⟨fun i j => congrArg σ (hX.herm i j), ?_⟩
    have e : (X.J.map σ).det = σ X.J.det := ((σ : E →+* E).map_det _).symm
    rw [e]
    exact (map_ne_zero σ).2 hd
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨q, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, -, hcov, ⟨C₀, hC₀, hconj⟩, -⟩ := hP F E σ hcm n _ hJ' q Xf Yf hW
  have hc'0 : 0 < min 1 c ^ q := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hh0⟩ := GlobalTheory.T.siegel_set_archimedean_norm_bound F E σ hcm n _ q Xf Yf _ hc'0
  have hh : ∀ t : Fin q → ℝ, (∀ i, min 1 c ^ q ≤ t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ _ Xf Yf t a →
      (height σ _ a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah := fun t ht a ha =>
    hh0 t ht a ha.1 (GlobalTheory.T.torus_element_archimedean_matrix_form F E σ hcm n _ hJ' q Xf Yf hW t (fun i => hc'0.trans_le (ht i)) a ha)
  let mul2 : GAd σ ((1 : E) • X.J.map σ) × GAd σ ((1 : E) • X.J.map σ) → GAd σ ((1 : E) • X.J.map σ) :=
    fun p => p.1 * p.2
  have hCK : IsCompact (mul2 '' (C₀ ×ˢ (K : Set (GAd σ ((1 : E) • X.J.map σ))))) :=
    (hC₀.prod hK).image continuous_mul
  have hhc : Continuous fun g : GAd σ ((1 : E) • X.J.map σ) => (height σ ((1 : E) • X.J.map σ) g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨Bd, hBd⟩ := (hCK.image hhc).bddAbove
  have hfr : IsFrameU σ X.J (fun i k => Xf k i) (fun i k => Yf k i) := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [form_cols hσ, hW.xx]; simp
    · rw [form_cols hσ, hW.yy]; simp
    · rw [form_cols hσ, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨q, fun i k => Xf k i, fun i k => Yf k i, hfr, e.symm '' (mul2 '' (C₀ ×ˢ (K : Set _))), min 1 c ^ q,
    Ch * max Bd 0, Ah, hCK.image he', hc'0, fun g => ?_⟩
  obtain ⟨γ, hγ, s', ⟨p, hp, t, htc, a, ha, k, hk, rfl⟩, hgs⟩ := hcov (e g)
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
  have hmem : a⁻¹ * p * a * k ∈ mul2 '' (C₀ ×ˢ (K : Set _)) := ⟨(a⁻¹ * p * a, k), ⟨hconj p hp t htc a ha, hk⟩, rfl⟩
  refine ⟨(e.symm γ)⁻¹, inv_mem hr, t, e.symm a, e.symm (a⁻¹ * p * a * k), cone_low hc htc,
    GlobalTheory.T.torus_element_unitary_matrix_identity F E σ hcm n X.J hX.herm q Xf Yf t a ha _ rfl, ⟨_, hmem, rfl⟩, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hgs]
    group
  · have h1 : (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤
        (height σ _ a : ℝ) * (height σ _ (a⁻¹ * p * a * k) : ℝ) := by
      exact_mod_cast heightGL_mul_le F (e.symm a).1 (e.symm (a⁻¹ * p * a * k)).1
    have h2 := hh t (cone_low hc htc) a ha
    have h3 : (height σ _ (a⁻¹ * p * a * k) : ℝ) ≤ max Bd 0 :=
      (hBd ⟨_, hmem, rfl⟩).trans (le_max_left _ _)
    have h4 : (0 : ℝ) ≤ height σ _ a := NNReal.coe_nonneg _
    have h5 : (0 : ℝ) ≤ height σ _ (a⁻¹ * p * a * k) := NNReal.coe_nonneg _
    calc (ht (e.symm a * e.symm (a⁻¹ * p * a * k)) : ℝ) ≤ _ := h1
      _ ≤ (Ch * (1 + ∏ i, t i) ^ Ah) * max Bd 0 := mul_le_mul h2 h3 h5 (h4.trans h2)
      _ = Ch * max Bd 0 * (1 + ∏ i, t i) ^ Ah := by ring

end
end

