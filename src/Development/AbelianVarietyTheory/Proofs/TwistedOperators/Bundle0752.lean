import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionRankZeroExtRestriction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0744
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0743
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0719
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLatticesNonzeroLineVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a b : WO S₀ T) :
    symplO S T (d.ext0 T a) (d.ext0 T b) = symplO S₀ T a b := by
  have h := d.hO_ext T 0 0 0 0 a b
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplO, symplO, h]

theorem isHalf_mul_right {k l m : ℕ} {e : AE D} {u : Mx D k l} (p : Mx D l m) (hu : IsHalf e u) : IsHalf e (u ⬝ p) := by
  intro i j
  show e * ∑ r, u i r * p r j = ∑ r, u i r * p r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [← mul_assoc, hu i r]

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

open GlobalTheory.FinPl.VLast.KernPf (wittCoreRestrictionHom wittCoreRestrictionHom_apply wittDecomposition_rankZero_ext_restriction) in

theorem lastLat_rankZero (hψ : IsStdChar D ψ (-1)) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'')
    (Γ : AddSubgroup (WO J.W T)) (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X))
    (hX : ∀ u, u ∈ ΓX ↔ J.d.ext0 T (o.resT J.W₀ u).1 ∈ Γ ∧ (show WO J.W₀ (negSp L'') from (o.resT J.W₀ u).2) ∈ ΓL)
    (h₁ : ∃ f, VacG ψ J.W T Γ f ∧ f ≠ 0) (h₂ : ∃ f, VacG ψ J.W₀ (negSp L'') ΓL f ∧ f ≠ 0) :
    LastLat ψ J o Γ ΓL ΓX := by
  have s0 := @GlobalTheory.SplitScalar.symplO_zero_right D
  have mA : ∀ a : WO J.W₀ T, J.d.ext0 T a ∈ Γ → (o.resT J.W₀).symm (a, 0) ∈ ΓX := fun a ha => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨ha, zero_mem _⟩
  have mB : ∀ b : WO J.W₀ L'', (show WO J.W₀ (negSp L'') from b) ∈ ΓL → (o.resT J.W₀).symm (0, b) ∈ ΓX := fun b hb => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨by rw [map_zero]; exact zero_mem _, hb⟩
  have n : ∀ a b : WO J.W₀ L'', ψ (symplO J.W₀ L'' a b) = 1 → ψ (symplO J.W₀ (negSp L'') a b) = 1 := fun a b h => by
    have e : symplO J.W₀ (negSp L'') a b = -symplO J.W₀ L'' a b := by
      simp only [symplO, hO, negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [e, ← GlobalTheory.CjNeg.conj_psi hψ, h, map_one]
  have hA : ∀ e (u : WO J.W₀ T), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (u, 0)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, add_zero]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have hB : ∀ e (u : WO J.W₀ L''), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (0, u)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, zero_add]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have back : ∀ u : WO J.W T, J.d.ext0 T (wittCoreRestrictionHom J.d T u) = u := wittDecomposition_rankZero_ext_restriction J.d T
  refine ⟨fun (w : WO J.W₀ X) hw => ⟨⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun (u : WO J.W₀ L'') hu => n _ _ ?_,
    fun e he (u : WO J.W₀ L'') hu hh => n _ _ ?_⟩, ?_⟩
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.1 _ (mA _ hu')
    rw [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_snd, nsmul_zero, s0, add_zero] at this
    rw [← back u, ← map_nsmul, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.2 e he _ (mA _ hu') (hA e _ (isHalf_mul_right _ hh))
    rw [o.symplO_resT, AddEquiv.apply_symm_apply, s0, add_zero] at this
    rw [← back u, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have := hw.1 _ (mB u hu)
    rwa [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_fst, nsmul_zero, s0, zero_add] at this
  · have := hw.2 e he _ (mB u hu) (hB e u hh)
    rwa [o.symplO_resT, AddEquiv.apply_symm_apply, s0, zero_add] at this
  · obtain ⟨f₁, a₁, b₁⟩ := h₁
    obtain ⟨f₂, a₂, b₂⟩ := h₂
    refine ⟨f₁, f₂, a₁, a₂, b₁, b₂, ?_⟩
    show VacG ψ J.W₀ X _ (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂))
    refine ⟨o.isThetaFunO_boxT (GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero J.d T a₁.1) (GlobalTheory.CjNeg.theta_negT' hψ a₂.1),
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, map_nsmul (o.resT J.W₀), Prod.smul_fst, Prod.smul_snd, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        map_nsmul (J.d.ext0 T), a₁.2.1 _ h1, GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (a₂.2.1 _ h2)
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        a₁.2.2 e he _ h1 (GlobalTheory.RankZeroVac.isHalf_wittHyperbolicExtendByZero_apply J.d T (GlobalTheory.AscInh.isHalf_mul o.pA hh)), GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))
        (a₂.2.2 e he _ h2 (GlobalTheory.AscInh.isHalf_mul o.pB hh))

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem latCore_zero_split : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (u : WO (G.V (.core 1)) (G.V (.core 0))), u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.resT _ u).1 ∈ latRow G 0 ∧ (F.oz.resT _ u).2 ∈ lineLat F 0 := by
  intro D q T L μ0 hL sc G W M hM F hF h u
  have e1 := GlobalTheory.T.orthogonal_projection_preserves_depth_lattice D q T L μ0 hL sc G W M hM F hF
  have e2 := GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero D q T L μ0 hL sc G W M hM F hF h
  have hu : F.oz.jA ⬝ (F.oz.pA ⬝ u) + F.oz.jB ⬝ (F.oz.pB ⬝ u) = u := (F.oz.resT _).symm_apply_apply u
  have hl : F.oz.pB ⬝ u ∈ lineLat F 0 ↔ (F.oz.resT _).symm (0, F.oz.pB ⬝ u) ∈ latCore G 0 := Iff.rfl
  show u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.pA ⬝ u) ∈ latRow G 0 ∧ F.oz.pB ⬝ u ∈ lineLat F 0
  rw [hl, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB ⬝ (F.oz.pB ⬝ u)), ← e2]
  constructor
  · intro hm
    have ha := e1 u hm
    refine ⟨ha, ?_⟩
    have hb : F.oz.jB ⬝ (F.oz.pB ⬝ u) = u - F.oz.jA ⬝ (F.oz.pA ⬝ u) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hu
    rw [hb]; exact sub_mem hm ha
  · rintro ⟨ha, hb⟩
    rw [← hu]
    exact add_mem ha hb

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem lastLat_std : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  intro D q T L μ0 hL sc G W M hM F hF
  have hψ := W.ψ_std
  have hline0 : ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := GlobalTheory.T.exists_ne_zero_vacuum_besselLineLattice_rankZero D q T L μ0 hL sc G W M hM F hF
  refine ⟨fun ρ hρ => ?_, fun v h => ?_⟩
  · rcases ρ with _ | σ
    · exact hline0
    · obtain ⟨-, -, h3⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D q T L μ0 hL sc G W M hM F hF
      exact GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ hψ _ _ _ _ (G.sp.P_is (2 * (σ + 1) + 1) (by omega)).sd (h3 (σ + 1)) _ le_rfl
  · have hm : 0 < D.R.m := by omega
    have hdep := dep_vac W 0 hm
    refine lastLat_rankZero hψ (F.jac v 0 h) F.oz _ _ _ (latCore_zero_split D q T L μ0 hL sc G W M hM F hF h) ?_ hline0
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (W.vac 0), ⟨GlobalTheory.CjNeg.theta_negS' hψ hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.1 u hu))
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.2 e he u hu hh))
    · intro h0
      apply GlobalTheory.SeeSaw.Inh.vac_ne_zero (W.vac_is 0 hm)
      funext w
      have h1 := congrFun h0 w
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Pi.zero_apply, map_eq_zero] at h1
      exact (map_eq_zero (starRingEnd ℂ)).1 h1

end GlobalTheory.LastSeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0Trivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModulUnit

open GlobalTheory.ChiGrid

theorem exists_int_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have hne : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
    intro v' hv'
    by_contra hc
    push_neg at hc
    have hle : v'.asIdeal ≤ v.asIdeal := fun t ht => hc t ht
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : v' = v := HeightOneSpectrum.ext heq
    exact hv (this ▸ hv')
  choose! f hf using hne
  refine ⟨∏ v' ∈ P.S0, f v' ^ P.depth sc v', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', h⟩
    exact (hf v' hv').2 (v.isPrime.mem_of_pow_mem _ h)
  · rw [map_prod, Places.modul]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have e : ((P.w v').under (𝓞 D.host.F)).asIdeal = v'.asIdeal := by rw [P.under_w hv']
    have h1 : f v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := e ▸ (hf v' hv').1
    exact h1

end GlobalTheory.ModulUnit

theorem GlobalTheory.ModulUnit.idV_modul_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  intro D T L P sc v hv
  obtain ⟨t, ht, htm⟩ := GlobalTheory.ModulUnit.exists_int_mem_modul P sc v hv
  apply le_antisymm
  · exact GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v
  · rw [GlobalTheory.SeeSaw.idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hαv, a, ha, rfl⟩
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [GlobalTheory.IdVGen.tmul_eq ht α]
    obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα hαv
    refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * o, Ideal.mul_mem_right _ _ htm, by rw [map_mul]; rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjXCols

theorem exists_nat_smul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) (A : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Λ, (N : E) • (A *ᵥ s) ∈ Λ := by
  classical
  obtain ⟨gens, hg⟩ := hΛ.fg
  have key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ := fun g =>
    GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)
  choose z hz0 hz using key
  have hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ := by
    intro g
    rcases Int.natAbs_eq (z g) with h | h
    · have h1 := hz g
      rw [h, Int.cast_natCast] at h1
      exact h1
    · have h1 := hz g
      rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff] at h1
      exact h1
  refine ⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f := by
    rw [Submodule.span_le]
    intro g hgm
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm
    have hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k := hk
    show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ
    rw [hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hnat g) k
  rw [hg] at hle
  intro s hs
  exact hle hs

variable {D : D7}

theorem sum_mul_eq (S : HSp D) (N : ℕ) (Q M : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hQM : S.gram * Q = M * S.gram)
    (s : Fin S.rank → D.host.E) (j : Fin S.rank) :
    ∑ l, (∑ k, star (s k) * S.gram k l) * ((N : D.host.E) • Q) l j =
      ∑ k, star (((N : D.host.E) • (Mᴴ *ᵥ s)) k) * S.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) =
      Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

theorem rat_natCast_smul {m n : ℕ} (N : ℕ) (X : Matrix (Fin m) (Fin n) D.host.E) :
    (rat ((N : D.host.E) • X) : Mx D m n) = N • (rat X : Mx D m n) := by
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]

end GlobalTheory.ProjXCols

namespace GlobalTheory.ProjXCols

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem nsmul_projX_mem_latBig : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j := fun j hh => by
    injection hh with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨N, hN, hNs⟩ := exists_nat_smul_mulVec_mem _ hsd.1
    ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ
  refine ⟨N, hN, fun u hu => ?_⟩
  have e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) =
      u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) :
        Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank) := by
    rw [rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rfl
  rw [e1]
  refine GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu
  refine sum_mul_eq _ N _ _ ?_ s j
  simp only [HypDec.qX, Matrix.mul_assoc]

end GlobalTheory.ProjXCols
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingGlobalIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineKerW

theorem ker_p_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) ΦD x) (Φ₁D x) 0) → ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ Φ₁ hD hD₁ hp
  obtain ⟨l, hl, hγl⟩ := GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes D θ X e Γ.W hO.JX hθ γ hγ
  have hder' : ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hO.JX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x)
      (Φ₁D x) 0 := by
    intro x; have := hder x; simp only [hγl] at this; exact this
  obtain ⟨Ψ, hΨ, hsum⟩ := GlobalTheory.T.seesaw_doubling_hermitian_form hP D θ X e Bs Γ Xc om om' hO.JX hθ hT' l hl ΦD hΦD Φ₁D hder'
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT'.base.std
  have hΦF : Φ ∈ algF ψ θ true A B := by
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' ΦD hΦD
    rwa [IsDatum.fun_eq Γ.M ψ cA cA.surjective hD hD']
  choose Φ' hΦ'F hΦ'D using fun i => hO.algA' (Ψ i) (hΨ i).1
  have hsumD : ∀ s : Finset (Fin l.length), IsDatum Γ.M ψ cA (∑ i ∈ s, Ψ i) (∑ i ∈ s, Φ' i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (CoinvPass.isDatum_zero (M := Γ.M) (ψ := ψ) (crd := cA))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact CoinvPass.isDatum_add hψ (hΦ'D a) ih
  have hΦ₁ : Φ₁ = ∑ i, Φ' i := IsDatum.fun_eq Γ.M ψ cA cA.surjective hD₁ (hsum ▸ hsumD Finset.univ)
  rw [hΦ₁, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hl _ (List.get_mem l i)
  rw [hm.mapA.eql _ _ hi Φ hΦF (Φ' i) (hΦ'F i)
    (GlobalTheory.T.seesaw_unfolding_mellin hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' _ _ hi ΦD hΦD (Ψ i) (hΨ i).1
      (hΨ i).2 Φ (Φ' i) hD (hΦ'D i)), hp, map_zero]

end GlobalTheory.LineKerW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

theorem GlobalTheory.SquareAgree.kerPD_stabLie : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', ∀ Φ₁ ∈ algD Γ.M' Bs.ψ Bs.emb, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm γ hγ
    ΦD hΦD Φ₁D hΦ₁D hder
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨-, Φ, hΦF, hD, hp⟩ := (mem_kerPD hψ θ A₁ B Bs Γ cB p' ΦD).1 hΦD
  have hΦD' : ΦD ∈ algD Γ.M' Bs.ψ Bs.emb := ((mem_kerPD hψ θ A₁ B Bs Γ cB p' ΦD).1 hΦD).1
  obtain ⟨l, hl, hγl⟩ := GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes D θ X e Γ.W hO.JX hθ γ hγ
  have hder' : ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x)
      (Φ₁D x) 0 := by
    intro x; have := hder x; simp only [hγl] at this; exact this
  obtain ⟨Ψ, hΨ, hsum⟩ := GlobalTheory.T.seesaw_doubling_gram_model hP D θ X e Bs Γ Xc om om' hO.JX hθ hT l hl ΦD hΦD' Φ₁D hder'
  choose Φ' hΦ'F hΦ'D using fun i => hO.algB' (Ψ i) (hΨ i).1
  obtain ⟨Φ₁, hΦ₁F, hD₁⟩ := hO.algB' Φ₁D hΦ₁D
  refine (mem_kerPD hψ θ A₁ B Bs Γ cB p' Φ₁D).2 ⟨hΦ₁D, Φ₁, hΦ₁F, hD₁, ?_⟩
  have hsumD : ∀ s : Finset (Fin l.length), IsDatum Γ.M' ψ cB (∑ i ∈ s, Ψ i) (∑ i ∈ s, Φ' i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (CoinvPass.isDatum_zero (M := Γ.M') (ψ := ψ) (crd := cB))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact CoinvPass.isDatum_add hψ (hΦ'D a) ih
  have hΦ₁ : Φ₁ = ∑ i, Φ' i := IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD₁ (hsum ▸ hsumD Finset.univ)
  rw [hΦ₁, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hl _ (List.get_mem l i)
  rw [hm.mapB.eql _ _ hi Φ hΦF (Φ' i) (hΦ'F i)
    (GlobalTheory.T.isDer_of_hasDerivAt_kapX_oneP hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT _ _ hi ΦD hΦD' (Ψ i) (hΨ i).1
      (hΨ i).2 Φ (Φ' i) hD (hΦ'D i)), hp, map_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualModulusShift_half_mem_completedModulusHom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  first | exact @GlobalTheory.HalfOut.smul_mem_hatMx_of_mem_latBig | exact GlobalTheory.HalfOut.smul_mem_hatMx_of_mem_latBig | (intros; apply GlobalTheory.HalfOut.smul_mem_hatMx_of_mem_latBig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHomLatticeOwnAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.AscFin.latBig_ann_right : OnStd fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ u ∈ latBig G i, W.ψ (symplO _ _ u u') = 1) → u' ∈ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM F hF i hi u' hmx h
  have sdS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdT : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).1 i hi).2.2.2
  refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u' hmx).2 fun u hu => ?_
  rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardLatticeOffS0Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_off_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.AscFin.stdAt_pcBF | exact GlobalTheory.AscFin.stdAt_pcBF | (intros; apply GlobalTheory.AscFin.stdAt_pcBF <;> assumption)
end

