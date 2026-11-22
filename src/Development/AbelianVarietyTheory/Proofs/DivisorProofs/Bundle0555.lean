import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  first | (exact @GlobalTheory.Shin.kills_self) | (exact GlobalTheory.Shin.kills_self) | (intros; apply GlobalTheory.Shin.kills_self  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitaryStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) → IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ) := by
  first | exact @GlobalTheory.RatUnit.isUA_ratM | exact GlobalTheory.RatUnit.isUA_ratM | (intros; apply GlobalTheory.RatUnit.isUA_ratM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R : Type} [CommRing R]

theorem sec_map_res' {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map ψ (Sec.res g z) = Sec.res g (Sec.map ψ z) :=
  congrArg (fun f => f.hom z) (ψ.hom.naturality g.op)

theorem sec_map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem flatS_of_iso {M N : Shv R} (i : M ≅ N) (h : FlatS M) : FlatS N := by
  obtain ⟨P, φ, hs, hi, hf⟩ := h
  refine ⟨P, φ ≫ i.hom.hom, ?_, ?_, hf⟩
  · intro U y
    obtain ⟨S, hS, hP⟩ := hs U (Sec.map i.inv y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    change Sec.map i.hom ((φ.app (op V)).hom x) = Sec.res g y
    rw [hx, sec_map_res', ← sec_map_comp', i.inv_hom_id, sec_map_id']
  · intro U x hx
    refine hi U x ?_
    have h1 : Sec.map i.inv (Sec.map i.hom ((φ.app (op U)).hom x)) = Sec.map i.inv (0 : Sec N U) :=
      congrArg (Sec.map i.inv) hx
    rw [← sec_map_comp', i.hom_inv_id, sec_map_id'] at h1
    exact h1.trans (map_zero _)

theorem flatS_of_isZero {M : Shv R} (h : IsZero M) : FlatS M := by
  have hsub : ∀ U : Scheme.{0}, Subsingleton (Sec M U) := fun U => by
    have h1 : IsZero M.obj := (sheafToPresheaf _ _).map_isZero h
    exact ModuleCat.subsingleton_of_isZero (((evaluation _ _).obj (op U)).map_isZero h1)
  refine ⟨M.obj, 𝟙 _, fun U y => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x _ => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => (hsub V).elim _ _⟩, fun U _ => ?_⟩
  haveI := hsub U
  change Module.Flat _ (Sec M U)
  infer_instance

theorem flatS_sgl {F : Shv R} (h : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact flatS_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm h
  · exact flatS_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

end

theorem isTwRes_tensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨hIge, εI, hεI, heI⟩ := hI
  obtain ⟨hJge, εJ, hεJ, heJ⟩ := hJ
  obtain ⟨μ, hμ, hμgen⟩ := GlobalTheory.T.tateTwist_mul_isTensorPairing q i j k hk
  obtain ⟨T₁, τ₁, hτ₁⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) J
  have hTge : T.IsStrictlyGE 0 := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.1 hIge hJge
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) μ hμ).1 τ₁ (𝟙 _) εJ
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ₁ hτ₁).1 τ εI (𝟙 J)
  obtain ⟨ν, hμν, -, hνt⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) μ
  obtain ⟨ν₁, hν₁, -, hν₁t⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) τ₁
  have hflati : ∀ t, FlatS ((sgl (tw q i)).X t) := flatS_sgl (flatS_tw q i)
  have hid : ∀ {K : Cx (ZMod q)} (t : ℤ) {U : Scheme.{0}} (x : Sec (K.X t) U), Sec.map (HomologicalComplex.Hom.f (𝟙 K) t) x = x :=
    fun _ _ _ => rfl
  haveI := hIge
  haveI := hJge
  haveI := hεI
  haveI := hεJ
  have hc : ν.Compat ν₁ εJ (𝟙 _) u₁ := by
    intro U s t w h a b
    rw [hμν U t s w (by omega) b a, hid, hν₁ U t s w (by omega) b (Sec.map (εJ.f s) a), Units.smul_def,
      Units.smul_def]
    have h1 := hu₁ U t s w (by omega) b a
    rw [hid] at h1
    rw [← h1]
    exact map_zsmul ((u₁.f w).hom.app (op U)).hom _ _
  have hq1 : QuasiIso u₁ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) ν ν₁ (hνt hμ) (hν₁t hτ₁) hflati εJ u₁ hc
  have hq2 : QuasiIso u₂ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) τ₁ τ hτ₁ hτ hflat εI u₂ hu₂
  refine ⟨hTge, u₁ ≫ u₂, quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _, fun U ζ => ?_⟩
  rw [← hμgen U ζ]
  change Sec.map (u₂.f 0) (Sec.map (u₁.f 0) _) = _
  rw [hu₁ U 0 0 0 (add_zero 0), hu₂ U 0 0 0 (add_zero 0), hid, hid, heI, heJ]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restriction : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) = GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defect
  | exact GlobalTheory.EtC.RedChern.res_defect
  | (intros; apply GlobalTheory.EtC.RedChern.res_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletionStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_iff_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E), 1 ≤ M → (∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) → (((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔ ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x)) := by
  first | exact @GlobalTheory.LocGlob.stab_cong_iff_hat | exact GlobalTheory.LocGlob.stab_cong_iff_hat | (intros; apply GlobalTheory.LocGlob.stab_cong_iff_hat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.EulerLocVol

noncomputable def invPowHom (i : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ i)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

theorem inv_zeta_le_prod_primes : ∀ (i : ℕ), 2 ≤ i → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := by
  intro i hi P hP
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hs' : Summable (invPowHom i) := by
    have := Real.summable_one_div_nat_pow.2 (by omega : 1 < i)
    simpa [invPowHom] using this
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invPowHom i p‖ < 1 := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt P).2
  have hfilt : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  rw [hfilt] at hE
  have hfac : ∀ p ∈ P, 0 < 1 - ((p : ℝ) ^ i)⁻¹ := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast (hP p hp).one_lt) (by omega)
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1)
  have hpos : 0 < ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := Finset.prod_pos hfac
  have hle : ∏ p ∈ P, (1 - invPowHom i p)⁻¹ ≤ ∑' n : ℕ, invPowHom i n := by
    rw [← hE.tsum_eq]
    exact Summable.tsum_subtype_le (⇑(invPowHom i)) _ (fun n => by change 0 ≤ ((n : ℝ) ^ i)⁻¹; positivity) hs'
  have hz : ∑' n : ℕ, invPowHom i n = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    rw [hs'.tsum_eq_zero_add]
    simp [invPowHom, show i ≠ 0 by omega]
  rw [hz, Finset.prod_inv_distrib] at hle
  simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  calc (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ((∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hpos) hle
    _ = _ := inv_inv _

theorem le_locFactor_of_not_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    ¬ (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  intro E _ _ _ r v hr hnp
  let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold locFactor resOrder
  rw [if_neg hnp]
  have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

theorem tprod_locFactor_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧
      (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, g (Ideal.absNorm v.asIdeal) ≤ locFactor E r v := by
    intro v
    by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
    · exact GlobalTheory.T.local_factor_lower_bound E r v (by omega) hp
    · exact le_locFactor_of_not_prime E r v (by omega) hp
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, locFactor E r v := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, locFactor E r v := by
      refine Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => (g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)).trans (hloc v)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
      refine inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
      _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
      _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
      _ ≤ _ := s3
      _ = _ := s2.symm
      _ ≤ _ := s1
  have hle : (Z ^ fdeg E)⁻¹ ≤ ∏' v, locFactor E r v :=
    ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)
  have hpos : 0 < (Z ^ fdeg E)⁻¹ := by positivity
  refine ⟨hpos.trans_le hle, ?_⟩
  calc (∏' v, locFactor E r v)⁻¹ ≤ ((Z ^ fdeg E)⁻¹)⁻¹ := inv_anti₀ hpos hle
    _ = Z ^ fdeg E := inv_inv _

end GlobalTheory.EulerLocVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationPullbackInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_pullback_injective : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  first | (exact @GlobalTheory.EtC.MVEtale.mv_etale_mid) | (exact GlobalTheory.EtC.MVEtale.mv_etale_mid) | (intros; apply GlobalTheory.EtC.MVEtale.mv_etale_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.MapComapIso

theorem map_eq_comap_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by
  apply le_antisymm
  · calc K.map f = (K.map f).comap (inv f ≫ f) := by simp
      _ = ((K.map f).comap f).comap (inv f) := by rw [Scheme.IdealSheafData.comap_comp]
      _ ≤ K.comap (inv f) :=
          Scheme.IdealSheafData.comap_mono (inv f) ((Scheme.IdealSheafData.map_gc f).l_u_le K)
  · calc K.comap (inv f) ≤ ((K.comap (inv f)).comap f).map f :=
          (Scheme.IdealSheafData.map_gc f).le_u_l _
      _ = (K.comap (f ≫ inv f)).map f := by rw [Scheme.IdealSheafData.comap_comp]
      _ = K.map f := by simp

theorem map_comap_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by
  rw [map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp]
  simp

theorem map_comap_ideal_eq_of_isIso_restrict :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by
  intro W W' π U hq hiso τ V hVU
  have hpb := (isPullback_morphismRestrict π U).flip
  have hres : ((τ.comap π).map π).comap U.ι = τ.comap U.ι := by
    rw [GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' U (π ⁻¹ᵁ U) π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) hpb inferInstance hq (τ.comap π),
      ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      map_comap_of_isIso]
  have hle : V.1 ≤ Scheme.Hom.opensRange U.ι := by rw [Scheme.Opens.opensRange_ι]; exact hVU
  let V' : U.toScheme.affineOpens := ⟨U.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion U.ι hle⟩
  have himg : (⟨U.ι ''ᵁ V'.1, (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).2 V'.2⟩ :
      W.affineOpens) = V := by
    apply Subtype.ext
    change U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion ((τ.comap π).map π) U.ι V'
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion τ U.ι V'
  rw [hres, h2] at h1
  have h3 := Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso U.ι V'.1).inv).2 h1
  have h4 : ∀ A B : W.affineOpens, A = B →
      ((τ.comap π).map π).ideal A = τ.ideal A → ((τ.comap π).map π).ideal B = τ.ideal B := by
    rintro A B rfl h; exact h
  exact h4 _ V himg h3.symm

end GlobalTheory.MapComapIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentityStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixGroup_chart_density_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  first | exact @GlobalTheory.SUVol.DensChart.density_at_one | exact GlobalTheory.SUVol.DensChart.density_at_one | (intros; apply GlobalTheory.SUVol.DensChart.density_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDualStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_end_lattice_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) → Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.mem_endLat_of_trace_integral | exact GlobalTheory.LieDisc.mem_endLat_of_trace_integral | (intros; apply GlobalTheory.LieDisc.mem_endLat_of_trace_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticCoverWeilRepresentationStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_cover_weil_representation : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.metaplectic_euclidean_gaussian | exact GlobalTheory.metaplectic_euclidean_gaussian | (intros; apply GlobalTheory.metaplectic_euclidean_gaussian <;> assumption)
end

