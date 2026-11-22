import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0285
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.StdCharTotReal

section Local

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
      a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h x hx
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨k, hk⟩ := h b
      exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
    · intro h r
      obtain ⟨k, hk⟩ := h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
      exact ⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩
  rw [hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
    FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr (h d hd)

theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  have hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k := by
    intro a
    rw [hrat, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg] at hn
      have : -Algebra.trace ℚ F a = (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      rw [map_neg, hk]
      push_cast
      ring
  have hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F :=
    fun r => (integral_iff _).2 ⟨r, rfl⟩
  have hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1 := fun t ht =>
    GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const)
      (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht
  obtain ⟨a, s, hs, hz⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z
  rw [one_smul] at hz
  have hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t) := by
    intro t ht
    rw [hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]
  have h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k := by
    constructor
    · intro h r
      rw [← hone, map_mul, ← hmul _ (hO r)]
      exact h _ (hO r)
    · intro h t ht
      rw [hmul t ht]
      exact GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1})
        (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const)
        (fun r => by
          show χ _ = 1
          rw [← map_mul, hone]
          exact h r) t ht
  rw [h1, trace_int_iff]
  refine forall₂_congr fun d _ => ?_
  rw [← integral_iff, hz, add_mul, map_mul]
  refine forall_congr' fun v => ?_
  have h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := mul_mem (hs v) (hO d v)
  exact ⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩

theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

theorem psiV_ne_one_of_trace {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have key := (fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1
    (fun t _ => by rw [single_mul]; exact hn _) d hd v
  have h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z := by
    rw [single_mul, single_same]
    show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z
    rw [inv_mul_cancel_right₀ hd1]
  rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at key
  omega

theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]
  have hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  push_cast
  refine Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _
    fun w => ?_
  · rw [← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]
    exact congrArg InfinitePlace.mk hab
  · have := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
    exact Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)

end Local

theorem exists_psiV_ne_one : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ r, psiV F ψ v r ≠ 1 := by
  intro F _ _ hF ψ hψ hinf v
  refine psiV_ne_one_of_trace hψ (fun a => ?_) v
  rw [hinf, ← sum_places_eq_trace]
  refine congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

end GlobalTheory.StdCharTotReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLattices
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLocMove

variable {D : D7}

theorem isLattice_gmap' (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨hA.fg.map _, ?_⟩
  have : (Formalism.HermitianLatticesTheory.gmap g A : Set (VS D).V) = (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (A : Set (VS D).V) := rfl
  rw [this, ← Submodule.map_span, hA.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range g

theorem finrank_Vp_eq (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

end GlobalTheory.RatLocMove

namespace GlobalTheory.RatLocMove

open GlobalTheory.LocExt

variable {D : D7}

theorem localExtension_isometryFixingFrames_mem_localUnitary {u u' : D.what₂.Word}
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (h : GV D) (hh : h ∈ H0 F F') (p : PlF D)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Ext p h g') : g' ∈ (FP p).UW0 := by
  obtain ⟨hiso, hF, hF'⟩ := hh
  obtain rfl := locEquiv_unique p h g' hg
  refine Subgroup.subset_closure ⟨locEquiv_unitary Z p h hiso, fun b => ⟨?_, ?_⟩⟩
  · rw [(hB p).1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
    rw [map_smul, locEquiv_ext p h, hF b]
  · rw [(hB p).2.1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
    rw [map_smul, locEquiv_ext p h, hF' b]

theorem rat_ext_moves : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  intro D X Y u u' F F' w _ _ Z FP hB hRel
  refine ⟨fun g p => ⟨locEquiv p g, locEquiv_ext p g, fun g' h => locEquiv_unique p g g' h⟩,
    fun h hh p g' hg => localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p g' hg, ?_, ?_⟩
  · intro g p g' Λ hg
    obtain rfl := locEquiv_unique p g g' hg
    exact (locEquiv_img Z p g Λ).symm
  · intro h hh Λ y hov
    have hmem : ∀ p, locEquiv p h ∈ (FP p).UW0 := fun p =>
      localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p _ (locEquiv_ext p h)
    have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p)
    choose act hmv _ using hact
    let y' : Dat Z FP := fun p => (act p).smul ⟨locEquiv p h, hmem p⟩ (y p)
    have hmoves : ∀ p, LocNG.Datum.Moves (locEquiv p h) (y p) (y' p) := fun p =>
      ((hmv p) ⟨locEquiv p h, hmem p⟩ (y p) (y' p)).2 rfl
    refine ⟨y', ⟨isLattice_gmap' h Λ hov.1, fun p => ?_⟩, fun p => ⟨locEquiv p h, locEquiv_ext p h, hmoves p⟩⟩
    obtain ⟨τ, hτ, hL⟩ := hov.2 p
    have hm := (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p) (locEquiv p h) (hmem p) (y p) (y' p) τ hτ (hmoves p)).1
    refine ⟨_, hm, ?_⟩
    show LocNG.img (locEquiv p h) τ.abelian₂ = _
    rw [hL, locEquiv_img Z p h Λ]

end GlobalTheory.RatLocMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentFrameAdaptedAndInvMem
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_mono {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {j k : ℕ} (h : j ≤ k) :
    Xflag F j ≤ Xflag F k :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => lt_of_lt_of_le hi h)

theorem xsp_eq {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x; simp

theorem mem_orth_iff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (y : (VS D).V) :
    y ∈ orth (VS D) (Xsp F) ↔ ∀ x ∈ Xsp F, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inv_mem_of_map_le (n : GV D) (W : Submodule D.host.E (VS D).V) [FiniteDimensional D.host.E W]
    (h : ∀ x ∈ W, n x ∈ W) : ∀ x ∈ W, n⁻¹ x ∈ W := by
  have hle : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ W := by
    rintro _ ⟨y, hy, rfl⟩; exact h y hy
  have heq : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n W)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : n⁻¹ (n y) = y := n.symm_apply_apply y
  simpa [this] using hy

end GlobalTheory.NRatInv

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_fd {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.toFinite _)

theorem map_xflag {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) (k : ℕ) :
    ∀ x ∈ Xflag F k, n x ∈ Xflag F k := by
  intro x hx
  cases k with
  | zero =>
    have : Xflag F 0 = ⊥ := by
      show Submodule.span _ _ = ⊥
      simp
    rw [this, Submodule.mem_bot] at hx
    subst hx; simp
  | succ j =>
    have h1 := hn.2.1 j x hx
    have h2 := xflag_mono F (Nat.le_succ j) h1
    simpa using add_mem h2 hx

theorem adapt_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (VS D) D.R.rS T) (n : GV D),
    n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  intro D T F n hn
  obtain ⟨hiso, hfl, hor⟩ := hn
  have hn' : n ∈ NRat F := ⟨hiso, hfl, hor⟩
  refine ⟨⟨hiso, ?_⟩, ?_⟩
  · intro a
    induction a using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last D.R.rS) = F.fl.z := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [hz]
      have : F.fl.z ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff]
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact F.fl.z_orth i
        | zero => simp
        | add a b _ _ ha hb => simp [ha, hb]
        | smul c a _ ha => simp [ha]
      have := hor _ this
      simpa [xsp_eq] using this
    | cast i =>
      have he : frame F (Fin.castSucc i) = F.fl.e i := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [he]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
      simpa using hfl i.val _ hmem
  · refine ⟨inv_mem hiso, ?_, ?_⟩
    · intro j x hx
      haveI := xflag_fd F (j + 1)
      have hy := inv_mem_of_map_le n _ (map_xflag hn' (j + 1)) x hx
      have key := hfl j _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this
    · intro x hx
      haveI := xflag_fd F D.R.rS
      have hsp : ∀ y ∈ Xsp F, n⁻¹ y ∈ Xsp F := by
        rw [xsp_eq]; exact inv_mem_of_map_le n _ (map_xflag hn' D.R.rS)
      have hspn : ∀ y ∈ Xsp F, n y ∈ Xsp F := by
        rw [xsp_eq]; exact map_xflag hn' D.R.rS
      have hy : n⁻¹ x ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff] at hx ⊢
        intro e he
        have h1 : n⁻¹ (n e) = e := n.symm_apply_apply e
        have h2 := (inv_mem hiso) (n e) x
        rw [h1] at h2
        rw [h2]; exact hx _ (hspn e he)
      have key := hor _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this

end GlobalTheory.NRatInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitAndSmulCompletedLatticeLeAtLevelPrime
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.LocCong

set_option maxHeartbeats 1000000 in

theorem qsmul_latP_le_gS : ∀ (D : D7) (Z : LocDat D) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ sg : Loc.SplitG (Z.M (below D P)).L, (Z.M (below D P)).split = some sg ∧ ∀ (Λ : LV D) (v : Vp D (below D P)), v ∈ (locH Z (below D P)).smulLat (algebraMap (D.s.atP (below D P)).Fp (D.s.atP (below D P)).Ep (sg.q : (D.s.atP (below D P)).Fp)) (lattice₂ D Z.M (below D P) Λ) → v ∈ lattice₂ D Z.M (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D Z P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  obtain ⟨j, hne, hgg⟩ : ∃ j : Fin 2, D.host.g i ≠ D.host.g j ∧ gS D = D.host.g i * D.host.g j := by
    fin_cases i
    · exact ⟨1, D.host.g_ne, rfl⟩
    · exact ⟨0, D.host.g_ne.symm, by simp [gS, mul_comm]⟩
  have hsome : (D.s.atP p).split.isSome := (D.s_split p).2 (by
    rw [hchar]; fin_cases i <;> simp)
  obtain ⟨sg0, hsg0⟩ := Option.isSome_iff_exists.1 hsome
  have hag := (Z.agree p).2.2.2.2.2
  rcases hZs : (Z.M p).split with _ | sg
  · rw [hZs, hsg0] at hag; exact hag.elim
  rw [hZs, hsg0] at hag
  refine ⟨sg, rfl, ?_⟩
  have hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) := by
    rw [hag.2, sg0.q_eq, hchar]
  have hqO : (sg.q : 𝒪[(D.s.atP p).Fp]) = ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    apply Subtype.ext; rw [hq]; push_cast; rfl
  have hcop : Nat.Coprime (D.host.g i) (D.host.g j) :=
    (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hne
  have hbez : (1 : ℤ) = (D.host.g i : ℤ) * Int.gcdA (D.host.g i) (D.host.g j) +
      (D.host.g j : ℤ) * Int.gcdB (D.host.g i) (D.host.g j) := by
    have := Int.gcd_eq_gcd_ab (D.host.g i : ℤ) (D.host.g j : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at this
    exact_mod_cast this
  have hunit : IsUnit ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    have hqn : ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) ∈ IsLocalRing.maximalIdeal 𝒪[(D.s.atP p).Fp] := by
      rw [← hqO]; exact sg.q_irr.not_isUnit
    have h1 : IsUnit (1 - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hqn)
    have h2 : (1 : 𝒪[(D.s.atP p).Fp]) - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) =
        ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdB (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) := by
      have := congrArg (Int.cast : ℤ → 𝒪[(D.s.atP p).Fp]) hbez
      push_cast at this
      rw [this]; ring
    rw [h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp) = 1 := by
    refine ⟨((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_⟩
    have h1 : ((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]) * ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) = 1 := by
      have := hunit.unit.inv_mul
      rwa [IsUnit.unit_spec] at this
    have h2 := congrArg Subtype.val h1
    exact_mod_cast h2
  have hwO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) ∈ (Z.M p).L.O := by
    rw [(Z.agree p).2.2.2.1, (D.s.atP p).O_def]
    exact isIntegral_algebraMap
  have hsc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gS D : ℕ) : (D.s.atP p).Ep) := by
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hq, hgg]
    congr 1
    push_cast
    calc ((D.host.g i : ℕ) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) * ((w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp)) := by rw [hw, mul_one]
      _ = _ := by ring
  intro Λ v hv
  unfold Loc.HermSp.smulLat at hv
  refine (Submodule.span_le.2 ?_) hv
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hsc, mul_smul]
    have e : ((gS D : ℕ) : (D.s.atP p).Ep) • baseChange₂ D p x = baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • x) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact (lattice₂ D Z.M p _).smul_mem (⟨_, hwO⟩ : (Z.M p).L.O)
      (Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx, rfl⟩)
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o y _ hy =>
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • (o • y) =
        o • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • y) := by
      show _ • ((o : (D.s.atP p).Ep) • y) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.LocCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartAlmostIsometricNearOneStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySubgroupChart_almost_isometric_near_one : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, uMat g - 1 ∈ A → uMat h - 1 ∈ A → Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ → Real.sqrt (Formalism.REAL.hs (uMat h - 1)) < δ → ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ∧ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ≤ κ * ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ := by
  first | exact @GlobalTheory.GaugeSubLip.chart_almost_isometric | exact GlobalTheory.GaugeSubLip.chart_almost_isometric | (intros; apply GlobalTheory.GaugeSubLip.chart_almost_isometric <;> assumption)
end

