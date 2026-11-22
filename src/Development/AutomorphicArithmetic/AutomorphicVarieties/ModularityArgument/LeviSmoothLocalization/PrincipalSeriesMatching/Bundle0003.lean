import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.Loc2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.RsOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.EulOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AdSysOf
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Global.SemiLocal
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd

open private Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint Ad3P.SEGAux.charEig_cyc_inv Ad3P.SEGAux.algSat_eq from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

private theorem unif_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ : kˣ →* ℂˣ) (hμ : GroundTheory.LocalField.IsUnramifiedChar μ) : μ (unif k) = μ (GroundTheory.LocalField.unifUnit k) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  have hord := GroundTheory.LocalField.ord_unifUnit (K := k)
  have hle : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x ≤ 1 ↔ 0 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 0) hx
    rwa [GroundTheory.LocalField.mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  have hlt : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x < 1 ↔ 1 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 1) hx
    rwa [GroundTheory.LocalField.mem_valBall_one_iff] at h0
  have a1 := (hlt (unif k).ne_zero).1 h1
  have a2 := h2 _ ((hlt (GroundTheory.LocalField.unifUnit k).ne_zero).2 hord.ge)
  have a3 : ValuativeRel.valuation k ((GroundTheory.LocalField.unifUnit k * (unif k)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ a2 zero_le'
  have a4 := (hle (Units.ne_zero _)).1 a3
  rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord] at a4
  have a5 : GroundTheory.LocalField.ord ((unif k : kˣ) : k) = 1 := by omega
  have a6 := GroundTheory.LocalField.isUnramifiedChar_iff.1 hμ (unif k * (GroundTheory.LocalField.unifUnit k)⁻¹) (by
    rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord, a5]; simp)
  rwa [map_mul, map_inv, mul_inv_eq_one] at a6

private theorem charpoly_inv {M M' : Matrix (Fin 2) (Fin 2) ℂ} (h : M * M' = 1) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : M.charpoly = X ^ 2 - C (a + b) * X + C (a * b)) : M'.charpoly = (X - C b⁻¹) * (X - C a⁻¹) := by
  rw [Matrix.charpoly_fin_two] at hc
  have e0 := congrArg (eval 0) hc
  have e1 := congrArg (eval 1) hc
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : M.det = a * b := by simpa using e0
  have ht : M.trace = a + b := by
    rw [hd] at e1
    linear_combination -e1
  have hi : M' = (a * b)⁻¹ • M.adjugate := by
    rw [← Matrix.inv_eq_right_inv h, Matrix.inv_def, hd, Ring.inverse_eq_inv']
  have t' : M'.trace = b⁻¹ + a⁻¹ := by
    rw [hi, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    rw [Matrix.trace_fin_two] at ht
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    field_simp
    linear_combination ht
  have d' : M'.det = b⁻¹ * a⁻¹ := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one, hd] at this
    field_simp
    linear_combination this
  rw [Matrix.charpoly_fin_two, t', d']
  simp only [map_add, map_mul]
  ring

private theorem frobEig_unique {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := ((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ)
  have e2 := congrArg Polynomial.roots e
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e2

private theorem ev_under (K : Type) [Field K] [NumberField K] {Q : HeightOneSpectrum (𝓞 K) → Prop}
    (h : ∀ᶠ w in Filter.cofinite, Q w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ w : PlacesOver K v, Q w.1 := by
  refine Filter.eventually_cofinite.2 (((Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 ℚ)).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩

private theorem frobEig_geom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ A : ValuationSubring Ω, IsPlaceOver A v → (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV v) σ →
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom = X ^ 2 - C (a + b) * X + C (a * b)) :
    FrobEig ι ρ v {b⁻¹, a⁻¹} := fun A hA => by
  obtain ⟨h1, h2⟩ := h A hA
  refine ⟨h1, fun σ hσ => ?_⟩
  have e := h2 σ hσ
  rw [← Matrix.charpoly_map] at e ⊢
  have hm : (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom * (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpoly_inv hm ha hb e]
  simp

private theorem algSat_inj (n q : ℕ) (hq : q ≠ 0) {B B' : Multiset ℂˣ} (h : algSat n q B = algSat n q B') : B = B' := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'
  rw [Ad3P.SEGAux.algSat_eq, Ad3P.SEGAux.algSat_eq] at h
  exact Multiset.map_injective (fun x y e => Units.ext (mul_left_cancel₀ hc e)) h

private theorem algSat_three (q : ℕ) (t : ℂˣ) : algSat 3 q {t, 1, t⁻¹} = {(q : ℂ) * t, (q : ℂ), (q : ℂ) * (t⁻¹ : ℂˣ)} := by
  have h : ((((q : ℝ) ^ (((3 : ℝ) - 1) / 2) : ℝ)) : ℂ) = q := by
    have : (((3 : ℝ) - 1) / 2) = 1 := by norm_num
    rw [this, Real.rpow_one]
    simp
  simp [algSat, h]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adSysOf :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdSysOf := by
  intro l _ Ω _ _ _ ι N _ χ D g ρ hR hS K _ _ _ _ P hA
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, v ∉ D.bad :=
    Filter.eventually_cofinite.2 (by simpa using D.bad.finite_toSet)
  filter_upwards [hR, hl, hb, ev_under K hA.2] with v h1 h2 h3 h4 w
  obtain ⟨B, hB, hF⟩ := h4 w
  obtain ⟨α, β, e1, e2, e3⟩ := hS.2 v h3
  have hp : Ad3.pOf v = normV v := by
    simp [Ad3.pOf, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq' : Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w := (normVal ℚ K v w (1 : _ →* ℂˣ)).2.2.2
  have hnq : normV w.1 = normV v ^ fdeg w := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq'
  have hu : w.1.under (𝓞 ℚ) = v := HeightOneSpectrum.ext w.2.over.symm
  have e4 : D.ν v (unif (v.adicCompletion ℚ)) = α / β := (unif_val (D.ν v) (D.unr v h3)).trans e3
  have g1 : FrobEig ι ρ v {(β : ℂ)⁻¹, (α : ℂ)⁻¹} := by
    refine frobEig_geom ι ρ v α β α.ne_zero β.ne_zero fun A hA' => ?_
    refine ⟨(h1 A hA').1, fun σ hσ => ?_⟩
    rw [(h1 A hA').2 σ hσ, e1, e2, hp]
  have g2 := Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint ι ρ v _ _ (inv_ne_zero β.ne_zero) (inv_ne_zero α.ne_zero) g1
  have g3 := UpperTheory.frobenius_eigenvalues_twist ℚ Ω l ι 3 _ _ v _ _ g2 (Ad3P.SEGAux.charEig_cyc_inv ι v h2)
  have g4 := (UpperTheory.frobenius_power_compatibility ℚ K Ω l ι w.1 (fdeg w) (by rw [hu]; exact hnq)).1 3 _ _ (by rw [hu]; exact g3)
  have g5 := frobEig_unique hF g4
  have hnz : normV w.1 ≠ 0 := by
    have := Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  rw [e4]
  have hfin : B = {(α / β) ^ fdeg w, 1, ((α / β) ^ fdeg w)⁻¹} := by
    refine algSat_inj 3 (normV w.1) hnz (g5.trans ?_)
    rw [algSat_three, hnq]
    have hα := α.ne_zero
    have hβ := β.ne_zero
    have x1 : (((β : ℂ)⁻¹ / (α : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * (((α / β) ^ fdeg w : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm]
      congr 2
      field_simp
    have x3 : (((α : ℂ)⁻¹ / (β : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * ((((α / β) ^ fdeg w)⁻¹ : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm, ← inv_pow]
      congr 2
      field_simp
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [x1, x3]
    simp
  rw [← hfin]
  exact hB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AnEx
section
namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem anEx : AnEx := by
  intro hp k N _ hk χ hχ g
  obtain ⟨hf, he⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨D, rfl, hs, hfe⟩ := Ad3.R.rs_of Ad3.loc2 k N hk χ hχ g.f g.a hf he (hp k N hk χ hχ g)
  rcases Ad3.S.anOf g.a D hfe (Ad3.S.eulOf Ad3.S.shim N χ D g.f g.a hf he hs) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨D, rfl, hs, h⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NotDih
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

private theorem coset_trace {k Γ : Type} [Field k] [IsAlgClosed k] [Group Γ] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hirr : IsIrr (r.comp H.subtype)) (t : Γ)
    (ht : ∀ h ∈ H, (r (t * h) : Matrix (Fin 2) (Fin 2) k).trace = 0) : False := by
  obtain ⟨-, -, hmin⟩ := hirr
  let R : H →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp (r.comp H.subtype)
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R fun W hW => hmin W le_top fun s v hv => hW s v hv
  let L : Matrix (Fin 2) (Fin 2) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin 2) k k) ∘ₗ LinearMap.mulLeft k (r t : Matrix (Fin 2) (Fin 2) k)
  have hL : Submodule.span k (Set.range R) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have := ht h h.2
    rw [map_mul, Units.val_mul] at this
    exact this
  rw [hspan] at hL
  have hz : (r t : Matrix (Fin 2) (Fin 2) k) = 0 := by
    ext i j
    have h := hL (Submodule.mem_top (x := Matrix.single j i (1 : k)))
    have h2 : ((r t : Matrix (Fin 2) (Fin 2) k) * Matrix.single j i (1 : k)).trace = 0 := h
    simpa [Matrix.trace_mul_single] using h2
  have := (r t).isUnit.ne_zero
  exact this hz

private theorem loc_val (η : HeckeCharacter ℚ) (v : Ad3.Pl) (h : IsUnramifiedChar (localChar η v)) :
    ((localChar η v (unifUnit (Ad3.Qv v)) : ℂˣ) : ℂ) = (η (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding v (uniformizer v))) : ℂ) := by
  have h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]

private theorem hecke_ne_one {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M} (h : heckeCharacter ψ ≠ 1) : ψ ≠ 1 := by
  rintro rfl
  refine h ?_
  ext x
  rw [coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.one_apply (Units.isUnit _)]
  rfl

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.notDih :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NotDih := by
  rintro l _ Ω _ _ _ ι k N _ χ g ρ hc hirr hrep ⟨η, h1, h2, hev⟩
  obtain ⟨M, _, ψ, -, rfl⟩ := exists_heckeCharacter_eq (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, h2⟩)
  set δ : G ℚ Ω →* (Qbar l)ˣ := Chr.dirG ℚ Ω (ψ.ringHomComp ι.symm.toRingHom) with hδ
  have hδc : Continuous fun s => (δ s : Qbar l) := dirG_cont _

  obtain ⟨t, ht⟩ : ∃ t, (δ t : Qbar l) ≠ 1 := by
    obtain ⟨u, hu⟩ : ∃ u : (ZMod M)ˣ, ψ u ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hecke_ne_one h1 (MulChar.ext fun u => by rw [hall u, MulChar.one_apply (Units.isUnit _)])
    obtain ⟨t, rfl⟩ := (Chr.clsOnto Ω M).1 u
    refine ⟨t, fun h => hu ?_⟩
    rw [dirG_val] at h
    apply ι.symm.injective
    rw [map_one]
    exact h

  have hM : ∀ᶠ w : Ad3.Pl in Filter.cofinite, ¬ normV w ∣ M :=
    Filter.eventually_cofinite.2 (by simpa using fin_dvd (NeZero.ne M))
  have hS := Filter.eventually_cofinite.1 (hrep.and (hev.and hM))
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun s : G ℚ Ω => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) :=
    (Units.continuous_val.comp hc).matrix_trace.mul (hδc.sub continuous_const)
  have key : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) = 0 := fun s => by
    refine (isClosed_eq c1 continuous_const).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hw
    obtain ⟨hr, ⟨hu, hv⟩, hwM⟩ := hw
    have hAq := (over_iff hA _).2 dvd_rfl
    have hp := normV_prime w
    obtain ⟨htr, -⟩ := tr_det ι _ ((hr A hA).2 σ hσ)
    show _ = (0 : Qbar l)
    rcases hv with h0 | h0
    · have hpe : RationalSymbol.prime w = normV w := by
        rw [← absNorm_asIdeal, Ad3P.DihedralUnramifiedPlaces.normV_eq, Ad3.pOf]
      have h3 : ¬ RationalSymbol.prime w ∣ M := by rwa [hpe]
      have h4 := (loc_val _ w hu).symm.trans (congrArg Units.val h0)
      rw [coe_heckeCharacter_uniformizer _ h3, hpe] at h4
      have h5 : (δ σ : Qbar l) = 1 := by
        rw [hδ, dirG_frob _ hp hAq hwM hσ]
        show ι.symm (ψ _) = 1
        rw [h4, Units.val_one]
        exact map_one _
      rw [h5, sub_self, mul_zero]
    · have h0' : g.a (normV w) = 0 := by rw [Ad3P.DihedralUnramifiedPlaces.normV_eq]; exact h0
      rw [htr, h0', map_zero, zero_mul]
  have hker : IsOpen (δ.ker : Set (G ℚ Ω)) := dirG_open _
  refine coset_trace ρ δ.ker (hirr _ hker) t fun h hh => ?_
  have h3 := key (t * h)
  have h4 : (δ (t * h) : Qbar l) = δ t := by rw [map_mul, MonoidHom.mem_ker.1 hh, mul_one]
  rw [h4] at h3
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 ht)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  have h := Classical.epsilon_spec (p := fun p : kˣ => valuation k (p : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k))
    ⟨Units.mk0 p hp0, by rw [Units.val_mk0, hp]; exact uniformizer_lt_one,
      fun x hx => by rw [Units.val_mk0, hp]; exact le_uniformizer_iff.2 hx⟩
  exact le_antisymm (le_uniformizer_iff.2 h.1) (hp ▸ h.2 p (hp ▸ uniformizer_lt_one))

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SphUnl := by
  intro K _ _ _ n hn π v B hB
  obtain ⟨⟨s₀, hs₀⟩, huniq, htor, hunr, -⟩ := suppFacts K n hn π v
  refine ⟨(htor s₀ hs₀).1.2 fun y hy => ?_, fun s hs => ?_⟩
  · obtain ⟨μ, hμ, rfl⟩ := hunr s₀ B hs₀ hB y hy
    rfl
  · obtain ⟨σ, hσ, -⟩ := id hs
    obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π v B).1 hB) hσ
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (v.adicCompletion K) n (fun i => unrChar _ (α i))
      (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hS.2.2
    have key : ∀ ξ ∈ chars s, ξ (unif _) ∈ B := by
      rintro ξ ⟨hξ, hm⟩
      rw [huniq s _ hs ⟨σ, hσ, h⟩] at hm
      obtain ⟨i, hi, e⟩ := Multiset.mem_map.1 hm
      rw [← IrrGL.ofChar_inj.1 e, unrChar_uniformizer _ _ (val_unif _), ← hα]
      exact Multiset.mem_map_of_mem _ hi
    intro ξ hξ ξ' hξ' _ e
    refine UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v B hB _ (key ξ hξ) _ (key ξ' hξ') ?_
    rw [← e, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel_right]
end

