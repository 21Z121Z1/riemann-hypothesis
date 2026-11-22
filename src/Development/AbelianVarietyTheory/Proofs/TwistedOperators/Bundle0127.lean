import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
section
open Formalism.BasicNotions IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.HermAdelicNorm

theorem congr_of_hasSignature {c p q : ℕ} {J J' : Matrix (Fin c) (Fin c) ℂ}
    (h : Formalism.UG.HasSignature J p q) (h' : Formalism.UG.HasSignature J' p q) :
    ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧ J' = Qᵀ * J * Q.map conj := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  set R : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P * P'⁻¹).val with hR
  have hRP : R * P'.val = P.val := by
    rw [hR, ← Units.val_mul, inv_mul_cancel_right]
  have h1 : Formalism.UG.cT (starRingEnd ℂ) R * J.reindex e e * R = J'.reindex e' e' := by
    have hu : IsUnit (Formalism.UG.cT (starRingEnd ℂ) (P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Formalism.UG.cT, Matrix.det_transpose,
        show ((P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det = _ from
          (RingHom.map_det (starRingEnd ℂ) _).symm]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 P'.isUnit).map _
    refine hu.mul_left_cancel (P'.isUnit.mul_right_cancel ?_)
    rw [hP', ← hP, ← hRP, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  let S : Matrix (Fin c) (Fin c) ℂ := R.submatrix e e'
  have hS : S.det ≠ 0 := by
    have : S * (P * P'⁻¹)⁻¹.val.submatrix e' e = 1 := by
      rw [Matrix.submatrix_mul_equiv, hR, Units.mul_inv, Matrix.submatrix_one_equiv]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  refine ⟨S.map conj, ?_, ?_⟩
  · rw [show (S.map conj).det = _ from (RingHom.map_det (starRingEnd ℂ) _).symm]
    exact (map_ne_zero _).2 hS
  · have h2 : (S.map conj).map conj = S := by
      ext a b
      simp
    have h3 : J' = (J'.reindex e' e').submatrix e' e' := by simp
    have h4 : J = (J.reindex e e).submatrix e e := by simp
    rw [h2, h3, ← h1]
    conv_rhs => rw [h4]
    rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e]
    rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_coord (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have h2 : star (2 : E) = 2 := star_ofNat 2
  obtain ⟨a, ha⟩ := (cm.fixed ((x + star x) / 2)).1 (by
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨b, hb⟩ := (cm.fixed ((x - star x) / (2 * θ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', h2, hθ]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

theorem exists_sq_sub (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) {d a : F}
    (hd : algebraMap F E d = θ * θ) (R : Type) [CommRing R] [Algebra F R] (y : E ⊗[F] R)
    (hy : Formalism.UG.sigR cm.sig R y * y = Formalism.UG.inclE R (algebraMap F E a)) :
    ∃ u w : R, algebraMap F R a = u ^ 2 - algebraMap F R d * w ^ 2 := by
  obtain ⟨u, w, rfl⟩ : ∃ u w : R, y = (1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w := by
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul x r =>
      obtain ⟨s, t, rfl⟩ := exists_coord cm h0 hθ x
      refine ⟨s • r, t • r, ?_⟩
      rw [TensorProduct.add_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨u, w, rfl⟩ := hx
      obtain ⟨u', w', rfl⟩ := hy
      exact ⟨u + u', w + w', by simp only [TensorProduct.tmul_add]; ring⟩
  refine ⟨u, w, Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := R)
    (algebraMap F E).injective ?_⟩
  have h1 : Formalism.UG.sigR cm.sig R ((1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w) =
      (1 : E) ⊗ₜ[F] u - θ ⊗ₜ[F] w := by
    rw [map_add]
    change (star (1 : E)) ⊗ₜ[F] u + (star θ) ⊗ₜ[F] w = _
    rw [star_one, hθ, TensorProduct.neg_tmul, sub_eq_add_neg]
  have h2 : ∀ s : F, ∀ r : R, (algebraMap F E s) ⊗ₜ[F] r = (1 : E) ⊗ₜ[F] (algebraMap F R s * r) := by
    intro s r
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have h3 : Formalism.UG.inclE (F := F) R (algebraMap F E a) = (1 : E) ⊗ₜ[F] (algebraMap F R a) := by
    rw [← mul_one (algebraMap F R a), ← h2]
    rfl
  rw [h1, h3] at hy
  simp only [Algebra.TensorProduct.includeRight_apply]
  rw [← hy, TensorProduct.tmul_sub, ← h2, hd, pow_two, pow_two,
    ← Algebra.TensorProduct.tmul_mul_tmul]
  rw [show ((1 : E) ⊗ₜ[F] (u * u) : E ⊗[F] R) = (1 : E) ⊗ₜ[F] u * (1 : E) ⊗ₜ[F] u by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
  ring

theorem congr_of_signature_of_adelic_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (c : ℕ) (G G' : Matrix (Fin c) (Fin c) E), Gᴴ = G → G'ᴴ = G' → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) → (∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F) (G.det / G'.det)) → ∃ P : Matrix (Fin c) (Fin c) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  intro F E _ _ _ _ _ _ cm c G G' hG hG' hd hd' hs ⟨y, hy⟩
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (cm.cmUnram.2.1 τ x).symm)
  have hH : ∀ {M : Matrix (Fin c) (Fin c) E}, Mᴴ = M →
      ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (M a b) = M b a := fun h a b => by
    rw [hcc]
    exact congrFun (congrFun h b) a
  have hs' : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj := fun τ => by
    obtain ⟨p, q, h, h'⟩ := hs τ
    exact congr_of_hasSignature h h'
  obtain ⟨a, ha⟩ := (cm.fixed (G.det / G'.det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hG'])
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  rw [hcc] at hθ
  obtain ⟨d, hdθ⟩ := (cm.fixed (θ * θ)).1 (by rw [star_mul', hθ]; ring)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h, map_zero])
  have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (by rw [← ha, h, map_zero])
  obtain ⟨u, w, huw⟩ := exists_sq_sub cm h0 hθ hdθ _ y (hy.trans (by rw [ha]))
  obtain ⟨s, t, hst⟩ := GlobalTheory.QNorm.hasseNormSt F d a hd0 ha0
    (fun ρ => by
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
      have h1 : τ (algebraMap F E a) = (Complex.ofRealHom.comp ρ) a :=
        ComplexEmbedding.lift_algebraMap_apply E _ a
      have h2 : 0 < (τ (G.det / G'.det)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hs' τ)
      rw [← ha, h1] at h2
      exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
    (fun v => by
      let ev : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) v
      have h1 := congrArg ev huw
      rw [map_sub, map_mul, map_pow, map_pow] at h1
      exact ⟨ev u, ev w, h1⟩)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E c G G'
    (hH hG) (hH hG') hd hd' hs' ⟨algebraMap F E s + algebraMap F E t * θ, by
      have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z :=
        fun z => (cm.fixed _).2 ⟨z, rfl⟩
      rw [hcc, star_add, star_mul', hf, hf, hθ, ← ha, hst, map_sub, map_mul, map_pow, map_pow, hdθ]
      ring⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [hPG]
    congr 2
    ext a b
    simp [hcc]

end GlobalTheory.HermAdelicNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.SmGL.SphCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem valuation_le_one_iff_adicValuation_le_one (x : v.adicCompletion F) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    (valuation (v.adicCompletion F)) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  have : Valuation.Compatible
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem residueFieldCard_adicCompletion_lemma :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = _root_.Formalism.UG.qV F v := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hmem : ∀ x : v.adicCompletion F,
      x ∈ 𝒪[v.adicCompletion F] ↔ x ∈ v.adicCompletionIntegers F := fun x => by
    simpa [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers] using
      valuation_le_one_iff_adicValuation_le_one v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x, (hmem x).1 x.2⟩
      invFun := fun x => ⟨x, (hmem x).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold _root_.GlobalTheory.SplitWeil.resCard
  rw [← _root_.Formalism.UG.P.tjcosets_card_residue v]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.ord_completion (x : (v.adicCompletion F)ˣ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SmGL.ord (v.adicCompletion F) x =
      -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have h := _root_.GlobalTheory.LGrp.BorelCompletion.nabs_completion v x
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow, residueFieldCard_adicCompletion_lemma] at h
  have hq : (1 : ℝ) < _root_.Formalism.UG.qV F v := by
    rw [← residueFieldCard_adicCompletion_lemma v]
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard _
  have := zpow_right_injective₀ (by linarith) hq.ne' h
  omega

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.KO_completion (n : ℕ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) = _root_.Formalism.UG.GLint (Fin n) (_root_.Formalism.UG.Ov F v) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  haveI := _root_.Formalism.UG.P.tjcosets_isLocalRing v
  ext g
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, _root_.Formalism.UG.P.tjcosets_mem_K_iff]
  simp only [Valuation.mem_integer_iff, _root_.Formalism.UG.P.cartan_mem_Ov, valuation_le_one_iff_adicValuation_le_one]

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem natCast_zpow_neg_cpow_eq_cpow_mul (q : ℕ) (m : ℤ) (n : ℕ) (i : Fin n) :
    (((q : ℝ) ^ (-m) : ℝ) : ℂ) ^ ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      (q : ℂ) ^ (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      ((((n : ℝ) - 1 - 2 * (i : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) =
      (((-m : ℝ) * (((n : ℝ) - 1 - 2 * (i : ℝ)) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (zpow_nonneg hq _), ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hq, Real.rpow_mul hq, ← Real.rpow_intCast]
  push_cast
  rfl

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.law_completion (n : ℕ) (α : Fin n → ℂˣ)
    (b : _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n)) (c : ℂ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    (_root_.GlobalTheory.SmGL.deltaHalf (v.adicCompletion F) (fun _ : Fin n => Unit)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
      ((_root_.GlobalTheory.SmGL.ofChar
          (_root_.GlobalTheory.SmGL.torusChar fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))).comp
        (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm.toMonoidHom)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) c =
      _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 * c := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  set t := _root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b with ht
  have hdet : ∀ i, ((Matrix.GeneralLinearGroup.det (t i) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = (b.1 : Matrix _ _ _) i i := by
    intro i
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact _root_.GlobalTheory.SmGL.leviProj_apply _ (_root_.GlobalTheory.SmGL.points (Fin n)) b i () ()
  have hsymm : ∀ i, (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm t i =
      Matrix.GeneralLinearGroup.det (t i) := fun i => rfl
  rw [_root_.GlobalTheory.SmGL.deltaHalf_apply]
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.ofChar_apply, smul_eq_mul,
    MulEquiv.coe_toMonoidHom, _root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.SmGL.unrChar_apply,
    hsymm, Units.coe_prod, _root_.GlobalTheory.SmGL.val_absPow]
  unfold _root_.Formalism.UG.chiDelta
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hord : _root_.GlobalTheory.SmGL.ord (v.adicCompletion F)
      (Matrix.GeneralLinearGroup.det (t i)) = _root_.Formalism.UG.ordV F v ((b.1 : Matrix _ _ _) i i) := by
    rw [_root_.GlobalTheory.SmGL.SphCompletion.ord_completion, _root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq, hdet]
  rw [_root_.GlobalTheory.SmGL.modExp_fin _ (fun _ => Fintype.card_unit),
    _root_.GlobalTheory.LGrp.nabs_eq_zpow, hord, residueFieldCard_adicCompletion_lemma, mul_comm]
  rw [Units.val_zpow_eq_zpow_val, natCast_zpow_neg_cpow_eq_cpow_mul]

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (φ : GL (Fin n) k → ℂ) :
    (∃ f ∈ _root_.GlobalTheory.PRep.fixed (_root_.GlobalTheory.SmGL.prinSeries χ)
        (_root_.GlobalTheory.SplitWeil.KO k (Fin n)), f.1.1 = φ) ↔
      (∀ (b : _root_.GlobalTheory.SmGL.borel k (Fin n)) g, φ (b * g) =
        (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
              (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) (φ g)) ∧
      ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n), ∀ x, φ (x * g) = φ x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed] at hf
    refine ⟨fun b g => _root_.GlobalTheory.SmGL.parInd_law _ _ f b g, fun g hg x => ?_⟩
    have := congrArg (fun f' => f'.1.1 x) (hf g hg)
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x f).symm.trans this
  · rintro ⟨hlaw, hinv⟩
    let f₀ : _root_.GlobalTheory.PRep.indSpace (_root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points (Fin n)))
        ((_root_.GlobalTheory.SmGL.twist
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
            (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
          (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit))).comp
          (_root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points (Fin n)))) :=
      ⟨φ, fun b g => hlaw b g⟩
    have hfix : ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
        _root_.GlobalTheory.PRep.ind _ _ g f₀ = f₀ := fun g hg => by
      ext x
      exact hinv g hg x
    have hsm : f₀ ∈ _root_.GlobalTheory.PRep.smoothPart (_root_.GlobalTheory.PRep.ind _ _) := by
      apply _root_.GlobalTheory.SmGL.mem_smoothPart_of_nhds
      refine Filter.mem_of_superset
        (_root_.GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (_root_.GlobalTheory.SplitWeil.KO k (Fin n)).one_mem)
        fun g hg => hfix g hg
    refine ⟨⟨f₀, hsm⟩, ?_, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed]
    intro g hg
    ext x
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x _).trans (hinv g hg x)

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in

theorem _root_.GlobalTheory.SmGL.SphCompletion.isSpherical_iff : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂˣ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ),
    letI := _root_.GlobalTheory.LocalData.complRel v; haveI := _root_.GlobalTheory.LocalData.isLocalField v;
    (_root_.Formalism.UG.IsSpherical F v (fun i => (α i : ℂ)) φ ↔
      ∃ f ∈ _root_.GlobalTheory.PRep.fixed
          (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))
          (_root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n)), f.1.1 = φ) := by
  intro F _ _ v n α φ
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hlaw := _root_.GlobalTheory.SmGL.SphCompletion.law_completion v n α
  have hone : _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) 1 = 1 := by
    unfold _root_.Formalism.UG.chiDelta
    simp [_root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq]
  have hborel : ∀ b : GL (Fin n) (v.adicCompletion F),
      _root_.Formalism.UG.IsUpperB F v b ↔ b ∈ _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n) := by
    intro b
    rw [_root_.GlobalTheory.SmGL.mem_borel]
    rfl
  rw [_root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff,
    _root_.GlobalTheory.SmGL.SphCompletion.KO_completion]
  unfold _root_.Formalism.UG.IsSpherical
  constructor
  · intro h
    refine ⟨fun b g => ?_, fun g hg x => ?_⟩
    · rw [hlaw b (φ g)]
      simpa only [mul_one] using h b g 1 ((hborel _).2 b.2) (one_mem _)
    · simpa only [one_mul, hone] using h 1 x g ((hborel 1).2 (one_mem _)) hg
  · rintro ⟨hL, hI⟩ b g k hb hk
    rw [hI k hk, ← hlaw ⟨b, (hborel b).1 hb⟩ (φ g)]
    exact hL ⟨b, (hborel b).1 hb⟩ g

end GlobalTheory.SmGL.SphCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProofStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PsiFinAlgebraic

theorem exists_pow_psi_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : ∃ M : ℕ, 0 < M ∧ ψ (pairA F 0 y) ^ M = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {c | ψ (pairA F 0 c) = 1}
    (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  obtain ⟨m, hm, hy⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral y
  refine ⟨N * m, Nat.mul_pos hN (Nat.pos_of_ne_zero hm), ?_⟩
  have h1 : ψ (pairA F 0 (N • m • y)) = 1 := h _ hy
  have e : pairA F 0 (N • m • y) = (N * m) • pairA F 0 y :=
    Prod.ext (smul_zero (N * m)).symm (mul_smul N m y).symm
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

theorem isAlgebraic_psi_fin {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : IsAlgebraic ℚ (ψ (pairA F 0 y)) := by
  obtain ⟨M, hM, h⟩ := exists_pow_psi_fin_eq_one hψ y
  refine IsAlgebraic.of_pow hM ?_
  rw [h]
  exact isAlgebraic_one

theorem isAlgebraic_psi_symplOH : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (u v : WO S T),
    u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)) := by
  intro D ψ hψ S T u v hu _
  have e : pairA D.host.F 0 (sndA D.host.F (symplOH S T u v)) = symplOH S T u v :=
    Prod.ext (GlobalTheory.WeilVacMove.fst_symplOH S T u v (Or.inl hu)).symm rfl
  rw [← e]
  exact isAlgebraic_psi_fin hψ.1 _

end GlobalTheory.PsiFinAlgebraic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isMultiplicityInner_of_unit_twist_shift : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  intro D V S θ M J χ μ 𝓕 hμ h𝓕 κ a ha hκ T hT T' hT' U U' hU hU' c hc
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold IsMultIP at hc ⊢
  intro v v'
  have haa : star a * a = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hfun : (fun g => star (U v g) * U' v' g) = fun g => star (T v (g * κ)) * T' v' (g * κ) := by
    funext g
    rw [hU, hU', star_mul']
    calc star a * star (T v (g * κ)) * (a * T' v' (g * κ))
        = (star a * a) * (star (T v (g * κ)) * T' v' (g * κ)) := by ring
      _ = star (T v (g * κ)) * T' v' (g * κ) := by rw [haa, one_mul]
  have hinv : ∀ γ ∈ GQ V, ∀ g, star (T v (γ * g)) * T' v' (γ * g) = star (T v g) * T' v' g := by
    intro γ hγ g
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ hγ g,
      (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ hγ g]
  have key := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 κ hκ
    (fun g => star (T v g) * T' v' g) hinv (hc v v').1
  rw [hfun]
  exact ⟨key.1, key.2.trans (hc v v').2⟩

end GlobalTheory
end

