import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS

theorem isProper_of_isQuot_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  intro k _ _ G _ X _ _ _ B _ i q hQ hB hX
  obtain ⟨hi, hq, hf, hsu, ha, hp, -⟩ := hQ
  have hsub : Subsingleton X := Module.finrank_zero_iff.1 hX
  have : Mono q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
  have := hB.proper
  have : Flat q.left := hf
  have : Surjective q.left := hsu
  have : IsAffineHom q.left := ha
  have : IsIso q.left := Flat.isIso_of_surjective_of_mono q.left
  rw [← Over.w q]
  infer_instance

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRealLine_blockEmbedding_exp_infinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∀ (v : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i j, ∀ u, u ≠ v → X i j u = 0) →
      IsRealLine σ J fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X))) := by
  first | exact @GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp | exact GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp | (intros; apply GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.WeilL2Words.StdArch

theorem supportedAtArchimedean_adeleOfMixedSpaceComponent (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (GlobalTheory.WeilL2Words.arch1 F z) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.WeilL2Words.arch1 F z) = z :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem isStdInf_of_isStd : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun z hz => ?_, fun z => ?_⟩
  · by_contra h
    push_neg at h
    exact hz (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace z fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)
  · rw [hψ.2.2 _ (supportedAtArchimedean_adeleOfMixedSpaceComponent F z), evI_arch1]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf

end GlobalTheory.WeilL2Words.StdArch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

theorem charR_hasDerivAt : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 →
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential

theorem biChar_contDiff : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) →
    (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) →
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter

section Phase

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

def phase (ψ : AddChar (AF F) ℂ) (M : ℝ →+ VA F N) (w : VA F N) (s : ℝ) : ℂ := ψ (⅟(2 : AF F) * symV w (M s))

theorem symV_add_left (w w' u : VA F N) : symV (w + w') u = symV w u + symV w' u := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_add_right (w u u' : VA F N) : symV w (u + u') = symV w u + symV w u' := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_zero_right (w : VA F N) : symV w 0 = 0 := by simp [symV]

theorem continuous_symV : Continuous fun p : VA F N × VA F N => symV p.1 p.2 := by
  unfold symV dotProduct
  fun_prop

theorem phase_add (M : ℝ →+ VA F N) (w : VA F N) (s s' : ℝ) :
    phase ψ M w (s + s') = phase ψ M w s * phase ψ M w s' := by
  simp only [phase, map_add, symV_add_right, mul_add, AddChar.map_add_eq_mul]

theorem phase_add_left (M : ℝ →+ VA F N) (w w' : VA F N) (s : ℝ) :
    phase ψ M (w + w') s = phase ψ M w s * phase ψ M w' s := by
  simp only [phase, symV_add_left, mul_add, AddChar.map_add_eq_mul]

theorem phase_zero (M : ℝ →+ VA F N) (w : VA F N) : phase ψ M w 0 = 1 := by
  simp [phase, symV_zero_right]

theorem continuous_phase (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) :
    Continuous fun p : VA F N × ℝ => phase ψ M p.1 p.2 := by
  have h1 : Continuous fun p : VA F N × ℝ => (p.1, M p.2) := by fun_prop
  have h2 : Continuous fun p : VA F N × ℝ => symV p.1 (M p.2) :=
    Continuous.comp (g := fun q : VA F N × VA F N => symV q.1 q.2) (f := fun p : VA F N × ℝ => (p.1, M p.2)) continuous_symV h1
  have h3 : Continuous fun p : VA F N × ℝ => ⅟(2 : AF F) * symV p.1 (M p.2) := continuous_const.mul h2
  exact hψ.comp h3

end Phase

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Crit

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem continuous_phase_right (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) :
    Continuous (phase ψ M w) := by
  have h : Continuous fun s : ℝ => ((w, s) : VA F N × ℝ) := by fun_prop
  exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2) (f := fun s : ℝ => ((w, s) : VA F N × ℝ))
    (continuous_phase hψ hM) h

theorem phase_hasDerivAt (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) (s : ℝ) :
    HasDerivAt (phase ψ M w) (deriv (phase ψ M w) 0 * phase ψ M w s) s :=
  charR_hasDerivAt _ (continuous_phase_right hψ hM w) (phase_add M w) (phase_zero M w) s

theorem contDiff_phase_deriv (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {k : ℕ}
    {L : (Fin k → ℝ) →+ VA F N} (hL : Continuous L) (u : VA F N) :
    ContDiff ℝ ∞ fun t => deriv (phase ψ M (u + L t)) 0 := by
  have e : (fun t => deriv (phase ψ M (u + L t)) 0) =
      fun t => deriv (phase ψ M u) 0 + deriv (phase ψ M (L t)) 0 := by
    funext t
    have hf : phase ψ M (u + L t) = fun s => phase ψ M u s * phase ψ M (L t) s := funext (phase_add_left M u (L t))
    have hd := ((phase_hasDerivAt hψ hM u 0).mul (phase_hasDerivAt hψ hM (L t) 0)).deriv
    simp only [phase_zero, mul_one, one_mul] at hd
    rw [hf]
    exact hd
  rw [e]
  have hQ : Continuous (Function.uncurry fun t s => phase ψ M (L t) s) := by
    have h : Continuous fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ) := by fun_prop
    exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2)
      (f := fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ)) (continuous_phase hψ hM) h
  exact contDiff_const.add (biChar_contDiff k (fun t s => phase ψ M (L t) s) hQ
    (fun t s s' => phase_add M (L t) s s') (fun t t' s => by simp only [map_add]; exact phase_add_left M _ _ s)
    (fun t => phase_zero M (L t)))

theorem hasDerivAt_lineV (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {f : VA F N → ℂ}
    {w : VA F N} {c : ℂ} (hd : HasDerivAt (fun s : ℝ => heisV ψ (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (phase ψ M w) 0 * f w) 0 := by
  have hp := phase_hasDerivAt hψ hM w 0
  have hne : ∀ s, phase ψ M w s ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * symV w (M s)) (-(⅟(2 : AF F) * symV w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
    have h0' : ψ (⅟(2 : AF F) * symV w (M s)) = 0 := h0
    rw [h0', zero_mul] at this
    exact one_ne_zero this
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisV ψ (M s) f w / phase ψ M w s := by
    funext s
    rw [heisV]
    exact (mul_div_cancel_left₀ _ (hne s)).symm
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisV ψ (M 0) f w = f w := by
    rw [heisV, map_zero, symV_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  rw [h1, phase_zero, mul_one]
  field_simp
  ring

theorem contDiff_of_heisV_closed (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (V : Set (VA F N → ℂ))
    (hc : ∀ f ∈ V, Continuous f)
    (hd : ∀ f ∈ V, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ V, ∀ w,
      HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (f' w) 0) :
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ VA F N), Continuous L → (∀ t, fin (L t).1 = 0 ∧ fin (L t).2 = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro f hf k L hL hLf u
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun G => ∃ f ∈ V, G = fun t => f (u + L t)
  refine GlobalTheory.Unf.MatCoef.contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h : Continuous fun t => u + L t := by fun_prop
    exact (hc f hf).comp h
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ VA F N := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    obtain ⟨f', hf', hD⟩ := hd f hf M ⟨hM, fun s => hLf _⟩
    refine ⟨2, ![fun _ => 1, fun t => -deriv (phase ψ M (u + L t)) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact (contDiff_phase_deriv hψ hM hL u).neg
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add, add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_lineV hψ hM (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end Crit

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}

theorem symplOHF_eq (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (w w' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ w w' = ⅟(2 : AF F) * symV (e w) (e w') := by
  rw [symplOHF, he, invOf_two_eq]

theorem heisOF_comp (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : WOF F E nS nT)
    (f : VA F N → ℂ) : heisOF σ JS JT ξ₀ ψ u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisOF, heisV, Function.comp_apply, symplOHF_eq he, map_add]

end Main

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem isThetaFunOF_thV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay F N B.ψ hR hψ Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add, symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h

end GlobalTheory.ThetaTransformF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExact
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open Limits

namespace GlobalTheory.SameLine

theorem injective_of_mem_range {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B' : Module.Basis (Fin 1) R M) (B : Module.Basis (Fin 1) R N)
    (f : M →ₗ[R] N) {t : M} (ht : f t = B 0) : Function.Injective f := by
  have hsum (P : Type) [AddCommGroup P] [Module R P] (C : Module.Basis (Fin 1) R P) (m : P) :
      m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  set c := B.repr (f (B' 0)) 0
  have hf (m : M) : B.repr (f m) 0 = B'.repr m 0 * c := by
    conv_lhs => rw [hsum M B' m]
    simp [c]
  have hac : B'.repr t 0 * c = 1 := by
    rw [← hf, ht]; simp
  refine (injective_iff_map_eq_zero f).2 fun m hm => ?_
  have h0 : B'.repr m 0 * c = 0 := by rw [← hf, hm]; simp
  have : B'.repr m 0 = 0 := by
    calc B'.repr m 0 = B'.repr m 0 * (B'.repr t 0 * c) := by rw [hac, mul_one]
      _ = B'.repr t 0 * (B'.repr m 0 * c) := by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hsum M B' m, this, zero_smul]

theorem isIso_of_epi {X : Scheme.{0}} {Q' Q : X.Modules} (π : Q' ⟶ Q) [Epi π]
    (hQ' : IsVB Q' 1) (hQ : IsVB Q 1) : IsIso π := by
  have : Mono π := by
    refine GlobalTheory.QCoh.mono_of_locally_app_injective π fun W x hx => ?_
    obtain ⟨U₁, e', -, hx₁, h₁, he'⟩ := hQ'.exists_affine hx
    obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
    obtain ⟨U₃, h₃, hx₃, t, ht⟩ := exists_app_eq_of_epi π (e 0) hx₂
    refine ⟨U₃, hx₃, h₃.trans (h₂.trans h₁), ?_⟩
    have := injective_of_mem_range (he'.basis (h₃.trans h₂)) (he.basis h₃)
      (GlobalTheory.QCoh.appLinear π U₃) (t := t) (by
        rw [GlobalTheory.QCoh.appLinear_apply, ht, IsFrame.basis_apply])
    exact this
  exact isIso_of_mono_of_epi π

end GlobalTheory.SameLine

theorem GlobalTheory.SameLine.eq_line : ∀ (X : Scheme.{0}) (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0), (ShortComplex.mk l m w).ShortExact → (ShortComplex.mk l' m' w').ShortExact → IsVB Q 1 → IsVB Q' 1 → l' ≫ m = 0 → ∃ e : L' ≅ L, e.hom ≫ l = l' := by
  intro X V L Q L' Q' l m w l' m' w' hS hS' hQ hQ' h
  have hmono : Mono l := hS.mono_f
  have hmono' : Mono l' := hS'.mono_f
  have hepi : Epi m := hS.epi_g
  obtain ⟨π, hπ⟩ := CokernelCofork.IsColimit.desc' hS'.gIsCokernel m h
  change Q' ⟶ Q at π
  change m' ≫ π = m at hπ
  have : Epi π := epi_of_epi_fac hπ
  have : IsIso π := GlobalTheory.SameLine.isIso_of_epi π hQ' hQ
  have h₂ : l ≫ m' = 0 := by
    rw [← cancel_mono π, Category.assoc]
    rw [hπ, w, zero_comp]
  obtain ⟨f, hf⟩ := KernelFork.IsLimit.lift' hS.fIsKernel l' h
  obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hS'.fIsKernel l h₂
  change L' ⟶ L at f
  change L ⟶ L' at g
  change f ≫ l = l' at hf
  change g ≫ l' = l at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_mono l', Category.assoc, hg, hf, Category.id_comp]
  · rw [← cancel_mono l, Category.assoc, hf, hg, Category.id_comp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderiv
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicSecondStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_hyperbolic_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∃ ι : GAd σ (c • Y₁.J.map σ) →* GAd σ (c • Y.J.map σ),
      (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 →
        ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 g₁ m ∧ m.1 = (ι g').1) ∧
      ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n₁) (Fin n₁) ℂ) (γ : ℝ → GAd σ (c • Y₁.J.map σ)),
        IsLineOf σ (c • Y₁.J.map σ) τ Z γ →
        IsLineOf σ (c • Y.J.map σ) τ (H.ι.map τ.1 * Z * (R.submatrix mid id).map τ.1) fun t => ι (γ t) := by
  first | exact @GlobalTheory.LeviEmbHC.leviEmb | exact GlobalTheory.LeviEmbHC.leviEmb | (intros; apply GlobalTheory.LeviEmbHC.leviEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentBisStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ Y₁.J) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H 1 h₁ m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H := by
  first | exact @GlobalTheory.LeviHC.levi_conj_mem_unip | exact GlobalTheory.LeviHC.levi_conj_mem_unip | (intros; apply GlobalTheory.LeviHC.levi_conj_mem_unip <;> assumption)
end

