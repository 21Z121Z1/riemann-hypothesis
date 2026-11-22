import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicFrameLagrangianFirstSummand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem conjTranspose_gram_mul_apply {D : D7} {n s t : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E)
    (A : Matrix (Fin n) (Fin s) D.host.E) (B : Matrix (Fin n) (Fin t) D.host.E) (a : Fin s) (c : Fin t) :
    (Aᴴ * G * B) a c = star (fun k => A k a) ⬝ᵥ G.mulVec (fun k => B k c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem exists_isoFrame_comap_inl : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
    ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  intro D W Y hY
  set I₁ := Y.1.comap (LinearMap.inl D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)) with hI₁
  have hpos : 0 < Module.finrank D.host.E I₁ :=
    Nat.pos_of_ne_zero fun h => hY (Submodule.finrank_eq_zero.mp h)
  let b := Module.finBasisOfFinrankEq D.host.E I₁ rfl
  have hsp : Submodule.span D.host.E (Set.range (I₁.subtype ∘ b)) = I₁ := by
    have h := congrArg (Submodule.map I₁.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  let I : Matrix (Fin W.rank) (Fin (Module.finrank D.host.E I₁)) D.host.E :=
    Matrix.of fun a j => (b j : Fin W.rank → D.host.E) a
  have hT : I.transpose = I₁.subtype ∘ b := by
    funext j a
    rfl
  refine ⟨_, I, ⟨hpos, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact b.linearIndependent.map' I₁.subtype (Submodule.ker_subtype I₁)
  · rw [GlobalTheory.MixModel.cT_sig]
    refine Matrix.ext fun a c => ?_
    rw [conjTranspose_gram_mul_apply, Matrix.zero_apply]
    have ha : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b a : Fin W.rank → D.host.E) ∈ Y.1 := (b a).2
    have hc : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b c : Fin W.rank → D.host.E) ∈ Y.1 := (b c).2
    have h := Y.2.2 _ ha _ hc
    simp only [LinearMap.inl_apply, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h
    exact h
  · rw [hT]
    exact hsp

end GlobalTheory.RawLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocks
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerParahoric

open GlobalTheory.LevelProduct

theorem exists_cut {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : GA D V) (hS : Lev.finE V h ∈ St β)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ k : GA D V, Lev.finE V k ∈ St β ∧ ∀ PP : Pl D.host.E,
      (PP.under (𝓞 D.host.F) ∈ S → redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h)) ∧
      (PP.under (𝓞 D.host.F) ∉ S → redFn β PP (Lev.finE V k) = 1) := by
  induction S using Finset.cons_induction_on with
  | empty =>
    refine ⟨1, ?_, fun PP => ⟨fun hh => absurd hh (Finset.notMem_empty _), fun _ => ?_⟩⟩
    · rw [MonoidHom.map_one]; exact Subgroup.one_mem _
    · rw [MonoidHom.map_one]; exact redFn_one PP
  | cons v S hv ih =>
    obtain ⟨k, hk, hr⟩ := ih
    have hc : Lev.finE V (cmp V v h) ∈ St β := by
      rw [finE_cmp]; exact piece_mem_St (phi_idem v) (phi_idem' v) hS
    have hpos : ∀ PP : Pl D.host.E, PP.under (𝓞 D.host.F) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = redFn β PP (Lev.finE V h) := fun PP e => by
      rw [finE_cmp]; exact redFn_piece (phi_idem v) (phi_idem' v) hS PP (resS_phi_pos e)
    have hneg : ∀ PP : Pl D.host.E, ¬ PP.under (𝓞 D.host.F) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = 1 := fun PP e => by
      rw [finE_cmp] at hc ⊢; exact redFn_piece_eq_one (phi_idem' v) hc PP (resS_phi_neg e)
    refine ⟨cmp V v h * k, ?_, fun PP => ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hc hk
    · rw [MonoidHom.map_mul, redFn_mul hc hk, Finset.mem_cons]
      by_cases e : PP.under (𝓞 D.host.F) = v
      · refine ⟨fun _ => ?_, fun hn => absurd (Or.inl e) hn⟩
        rw [hpos PP e, (hr PP).2 (e ▸ hv), mul_one]
      · rw [hneg PP e, one_mul]
        exact ⟨fun hh => (hr PP).1 (hh.resolve_left e), fun hh => (hr PP).2 fun h' => hh (Or.inr h')⟩

set_option maxHeartbeats 1600000 in

theorem exists_mem_smaller : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  classical
  intro D V β Λ _ L Q' xq hQ hoff g hg
  obtain ⟨_, h, rfl⟩ := g
  have hh : Lev.finE V h ∈ lev D.sp.cm V.gram β (Lev.flagL L) := hg
  obtain ⟨-, hS, hP, hq⟩ := mem_parLev.1 (lev_le_parLev hh)
  obtain ⟨k, hk, hr⟩ := exists_cut V β h hS (L.Pg.image fun PP => PP.under (𝓞 D.host.F))
  have h1 : ∀ PP ∈ L.Pg, redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h) := fun PP hPP =>
    (hr PP).1 (Finset.mem_image_of_mem _ hPP)
  have h2 : ∀ PP ∈ Q', redFn β PP (Lev.finE V k) = 1 := fun PP' hPP' => (hr PP').2 fun hm => by
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨a, b, -⟩ := hoff PP hPP PP' hPP'
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact a e'.symm
    · refine b ?_
      rw [e']
      exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩
  have hS' : Lev.finE V h⁻¹ ∈ St β := by rw [MonoidHom.map_inv]; exact Subgroup.inv_mem _ hS
  have h3 : ∀ PP, redFn β PP (Lev.finE V (h⁻¹ * k)) = (redFn β PP (Lev.finE V h))⁻¹ * redFn β PP (Lev.finE V k) :=
    fun PP => by rw [MonoidHom.map_mul, redFn_mul hS' hk, MonoidHom.map_inv, redFn_inv hS]
  have A : Lev.finE V k ∈ lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V k, hk, fun PP hPP => ?_, fun PP hPP => ?_⟩,
      Subgroup.mem_top _⟩
    · rw [h1 PP hPP]; exact hP PP hPP
    · rw [h2 PP hPP]; exact Subgroup.one_mem _
  have B : Lev.finE V (h⁻¹ * k) ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, ?_, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hS' hk
    · rw [h3, h1 PP hPP, inv_mul_cancel]; exact Subgroup.one_mem _
    · rw [h3, h2 PP (hQ hPP), mul_one]; exact Subgroup.inv_mem _ (hq PP hPP)
    · have e : rTup β (Lev.flag1L L) (Lev.finE V (h⁻¹ * k)) = 1 := by
        funext PP
        show upperLeftBlock L.hr (redFn β PP.1 (Lev.finE V (h⁻¹ * k))) = 1
        rw [h3, h1 PP.1 PP.2, inv_mul_cancel]; exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [e]; exact Subgroup.one_mem _
  refine ⟨(finHom V).rangeRestrict k, A, ?_⟩
  have e : (⟨finHom V h, h, rfl⟩ : Bridge.Gf V)⁻¹ * (finHom V).rangeRestrict k = (finHom V).rangeRestrict (h⁻¹ * k) := by
    apply Subtype.ext
    exact ((MonoidHom.map_mul (finHom V) _ _).trans (congrArg (· * finHom V k) (MonoidHom.map_inv (finHom V) h))).symm
  rw [e]
  exact B

end GlobalTheory.SmallerParahoric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem onB_mulLeft_mem_Dst_of_fixed {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V)
    (a : Bst P) (ha : ∀ g : ↥(GK K), actSt P (g : GQ l) a = a) (x : V ⊗[ℚ_[l]] Bst P)
    (hx : x ∈ Dst P ρ) : onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x ∈ Dst P ρ := by
  rw [mem_Dst] at hx ⊢
  intro g
  have h : stRep P ρ g * onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) =
      onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) * stRep P ρ g :=
    end_ext P fun v b => by
      simp only [End.mul_apply, onB_tmul, stRep_tmul, LinearMap.mulLeft_apply, map_mul, ha]
  rw [← End.mul_apply, h, End.mul_apply, hx]

theorem exists_pairing_Dst_Dcris_phi_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hd hs
  obtain ⟨pr, hφ, hN, hg, hmul, hnd⟩ := GlobalTheory.T.exists_semistable_tensor_pairing_of_dual l P K V V' ρ ρ' m hd
  obtain ⟨lam, hlφ, hlnd⟩ := GlobalTheory.T.exists_linearForm_semistable_extending_trace l P K
  let W := Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)
  let j : ↥W →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := (crisIncl P ℚ_[l] V') ∘ₗ W.subtype
  have hj : ∀ w : ↥W, j w = crisIncl P ℚ_[l] V' (w : V' ⊗[ℚ_[l]] P.R.B) := fun _ => rfl
  have hjg : ∀ (w : ↥W) g, stRep P ρ' g (j w) = j w := by
    intro w g
    have h1 := w.2.1
    have h2 : actVB (P.PD K) ρ' g (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := (Submodule.mem_iInf _).mp h1 g
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [hj, stRep_crisIncl, h2]
  have hjN : ∀ w : ↥W, monV P ℚ_[l] V' (j w) = 0 := fun w =>
    (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V' _).mpr ⟨_, (hj w).symm⟩
  have hjφ : ∀ w : ↥W, phiV P ℚ_[l] V' (j w) = j w := by
    intro w
    have h2 : φVB (P.PD K) (LL := ℚ_[l]) (V := V') (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := w.2.2
      rwa [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at this
    rw [hj, GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K, h2]
  have hinv : ∀ x ∈ Dst P ρ, ∀ w : ↥W, ∃ c : ↥(K0 K), Polynomial.C P.tB * pr x (j w) =
      Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
    intro x hx w
    refine (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mp fun g => ?_
    have h1 := hg g x (j w)
    rw [(mem_Dst P ρ).mp hx g, hjg] at h1
    rw [map_mul, actSt_C, localPrime_galoisAction_periodT, ← Polynomial.smul_C, smul_mul_assoc, ← mul_smul_comm, ← h1]
  let B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥W →ₗ[ℚ_[l]] ℚ_[l] :=
    (pr.compl₂ j).compr₂ (lam ∘ₗ LinearMap.mulLeft ℚ_[l] (Polynomial.C P.tB))
  have hB : ∀ x w, B x w = lam (Polynomial.C P.tB * pr x (j w)) := fun _ _ => rfl
  refine ⟨B, fun x hx w => ?_, fun x hx w => ?_, fun w hw => ?_⟩
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hN x (j w)
    rw [hjN, map_zero, add_zero] at h1
    rw [hB, h1, ← monSt_C_mul, hc, (monSt_eq_zero_iff P _).mpr ⟨_, rfl⟩, map_zero]
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hφ x (j w)
    rw [hjφ] at h1
    rw [hB, hB, map_smul, LinearMap.smul_apply, h1, mul_smul_comm, ← smul_mul_assoc,
      Polynomial.smul_C, ← localPrime_frobenius_periodT, ← phiSt_C, ← map_mul, hc, hlφ]
  · have h0 : ∀ x ∈ Dst P ρ, pr x (j w) = 0 := by
      intro x hx
      obtain ⟨c, hc⟩ := hinv x hx w
      have hc0 : c = 0 := by
        refine hlnd c fun c' => ?_
        have h2 := hw _ (onB_mulLeft_mem_Dst_of_fixed P ρ _
          ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mpr ⟨c', rfl⟩) x hx)
        rw [hB, hmul, mul_left_comm, hc] at h2
        exact h2
      rw [hc0, map_zero, map_zero] at hc
      exact ((isUnit_tB P).map Polynomial.C).mul_right_eq_zero.mp hc
    have h1 : j w = 0 := by
      refine hnd _ fun v => ?_
      obtain ⟨k, a, x, hx, hv⟩ := GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K V ρ hs v
      rw [hv, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hmul, h0 _ (hx i), mul_zero]
    apply Subtype.ext
    apply crisIncl_injective P (LL := ℚ_[l])
    rw [← hj, h1]
    simp

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

theorem sst_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hC d ρ hsst
  have hdr := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  obtain ⟨b, c, hb, hfix, hlog⟩ := GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods l K bk P AI T C hC trivial
  obtain ⟨U, U', c₁, c₃, k, F, F', Mn, hUU', hFF', hφ, hMn, hgal⟩ := GlobalTheory.T.semistable_periodMatrix_at_log_zero l K bk P AI T C hC d ρ b c hb hsst
  obtain ⟨-, hInvdR⟩ := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨lam, hlamg, hlamA⟩ := GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle l K bk P AI T C hC b c hb hfix hlog
  obtain ⟨Λ₀, hΛ₀g, hΛ₀A⟩ := GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx l K bk P AI T C hC d (fun g => (ρ g).val) U k Mn c hMn hgal lam hlamg hlamA
  obtain ⟨e, m, hm, hdf⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l (Fact.out : l.Prime).ne_one
  have hk₀ : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l (e + k * d) k i‖ ≤ 1 := fun i hi => GlobalTheory.SstPer.ecoefQ_norm_le k hm hdf hi
  obtain ⟨N₀, hZ⟩ := GlobalTheory.T.semistable_periods_over_Acris l K bk P AI T C hC d (fun g => (ρ g).val) U U' hUU' c₁ F hφ k (e + k * d) Mn c hk₀ hgal
  have hUUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨N, c₂, X, X', hN, hXX', hX, hX'⟩ := GlobalTheory.T.exists_twisted_modification_at_E l K bk C hInvdR d (fun g => (ρ g).val) H (U.map C.ι) (U'.map C.ι) Λ₀ hUUι hΛ₀g hΛ₀A N₀
  obtain ⟨Z, Z', hZZ', hZφ, hZg, hZX, hZX'⟩ := hZ N hN X X' hX hX'
  refine ⟨N, c₁, c₂, c₃, e + k * d, F, F', X, X', Z, Z', fun g => GlobalTheory.SstPer.kap C bk (e + k * d) k Mn (c g), hFF', hXX', hZZ', hZφ, hZg, ?_, hZX, hZX', GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil l K bk P AI T C hC d k (e + k * d) Mn c hk₀ hMn hlog⟩
  intro g hg
  simp only
  rw [hfix g hg]
  exact GlobalTheory.SstPer.kap_zero C bk _ k Mn

end GlobalTheory.SstPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.JumpsOfM

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hF l _ a e _ _ ϖ LL _ hT hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN U hU i hi
  obtain ⟨x, hfix, hx, hx'⟩ := GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin hF l a e ϖ LL hl ι P T I jB Pl AI hStd hCmp hHor hEN i hi
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by rw [← hT.succ_eq]; simp⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  let τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1 :=
    (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact hU τ i (GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector l Pl LL T (ϖ.field a) hG i x hfix hx hx' τ)

end GlobalTheory.JumpsOfM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CongIndex

theorem bounded_cover {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {J : Subgroup (GAf L n)}
    (hJ : IsBounded J) {M : ℕ} (hM : 0 < M) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n M (f⁻¹ * κ) := by
  classical
  obtain ⟨F0, hF0⟩ := hJ
  obtain ⟨F1, hF1⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hM
  refine ⟨(F0 ×ˢ F1).image (fun p => p.1 * p.2), fun κ hκ => ?_⟩
  obtain ⟨f0, hf0, hu⟩ := hF0 κ hκ
  obtain ⟨j, hj, κ', hκ', e⟩ := hF1 _ hu
  refine ⟨f0 * j, Finset.mem_image.2 ⟨(f0, j), Finset.mem_product.2 ⟨hf0, hj⟩, rfl⟩, ?_⟩
  have h1 : (f0 * j)⁻¹ * κ = κ' := by
    rw [mul_inv_rev, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h1]
  exact hκ'

theorem finite_index_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ (h : GAf L n) (N : ℕ), 0 < N →
      (∃ N' : ℕ, 0 < N' ∧ ∀ κ, NG.Cong L n N' κ → NG.Cong L n N (h⁻¹ * κ * h)) ∧
      (∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n N (f⁻¹ * κ)) ∧
      IsBounded (J.map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n J hJ h N hN
  refine ⟨GlobalTheory.CongConjugate.congConj L n h N hN, bounded_cover hJ hN, ?_⟩
  classical
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h⁻¹ 1 one_pos
  obtain ⟨F, hF⟩ := bounded_cover hJ hN'
  refine ⟨F.image (fun f => h * f * h⁻¹), fun x hx => ?_⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨f, hf, hcf⟩ := hF κ hκ
  refine ⟨h * f * h⁻¹, Finset.mem_image_of_mem _ hf, ?_⟩
  have hu := (hc _ hcf).1
  have e : (h * f * h⁻¹)⁻¹ * (MulAut.conj h).toMonoidHom κ = h⁻¹⁻¹ * (f⁻¹ * κ) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact hu

end GlobalTheory.CongIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddFStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  first | exact @GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | exact GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | (intros; apply GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedAlgebraicOfLimitOfFixedElements
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixApprox

theorem val_lt_map {K : Type} [Field K] (B : ValuationSubring K) (τ : K ≃+* K)
    (hB : ∀ z, τ z ∈ B ↔ z ∈ B) (a b : K) (h : B.valuation a < B.valuation b) :
    B.valuation (τ a) < B.valuation (τ b) := by
  have hb : b ≠ 0 := by
    rintro rfl; simp at h
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero]
    exact (Valuation.pos_iff _).2 (by simpa using hb)
  · have hta : τ a ≠ 0 := by simpa using ha
    rw [← not_le] at h ⊢
    intro h'
    apply h
    have h1 : B.valuation (τ b / τ a) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hta)]; exact h'
    rw [ValuationSubring.valuation_le_one_iff, ← map_div₀, hB] at h1
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 ha)] at h1
    exact h1

theorem fix_of_approx : ∀ (K : Type) [Field K] [CharZero K] (B : ValuationSubring K) (τ : K ≃+* K), (∀ z, τ z ∈ B ↔ z ∈ B) → ∀ y : K, IsAlgebraic ℚ y → (∀ δ : K, δ ≠ 0 → ∃ u : K, τ u = u ∧ B.valuation (y - u) < B.valuation δ) → τ y = y := by
  intro K _ _ B τ hB y _ happ
  by_contra hne
  set m := τ y with hm
  set s := τ.symm y with hs
  have hym : y - m ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hys : y - s ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg τ (sub_eq_zero.1 h)
    rw [hs, RingEquiv.apply_symm_apply] at h'
    exact h'
  obtain ⟨u, hu, hlt⟩ := happ (if B.valuation (y - m) ≤ B.valuation (y - s) then y - m else y - s)
    (by split_ifs <;> assumption)
  have h1 : B.valuation (y - u) < B.valuation (y - m) := by
    split_ifs at hlt with hc
    · exact hlt
    · exact lt_of_lt_of_le hlt (le_of_lt (not_le.1 hc))
  have h2 : B.valuation (y - u) < B.valuation (y - s) := by
    split_ifs at hlt with hc
    · exact lt_of_lt_of_le hlt hc
    · exact hlt
  have h3 := val_lt_map B τ hB _ _ h2
  have e1 : τ (y - u) = m - u := by rw [map_sub, hu]
  have e2 : τ (y - s) = m - y := by rw [map_sub, hs, RingEquiv.apply_symm_apply]
  rw [e1, e2] at h3
  have h4 : B.valuation (m - y) = B.valuation (y - m) := Valuation.map_sub_swap _ _ _
  have h5 : m - y = (m - u) - (y - u) := by ring
  have h6 : B.valuation (m - y) < B.valuation (m - y) := by
    calc B.valuation (m - y) = B.valuation ((m - u) - (y - u)) := by rw [← h5]
      _ < B.valuation (m - y) := Valuation.map_sub_lt _ h3 (h4 ▸ h1)
  exact lt_irrefl _ h6

end GlobalTheory.FixApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUniqueStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalArtinReciprocityMap_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  first | exact @GlobalTheory.ArtinUniq.globalArtin_unique | exact GlobalTheory.ArtinUniq.globalArtin_unique | (intros; apply GlobalTheory.ArtinUniq.globalArtin_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem h1f_generators_of_record : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  intro D l _ K LL _ T _
  exact GlobalTheory.T.h1f_generated_lattice l (D.loc l) (D.locA l) (D.locT l) K LL T

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polynomial_eq_zero_of_function : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  first | exact @GlobalTheory.ExportSeries.HarmInj.harm_inj | exact GlobalTheory.ExportSeries.HarmInj.harm_inj | (intros; apply GlobalTheory.ExportSeries.HarmInj.harm_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_isSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.sst_isDR | exact GlobalTheory.sst_isDR | (intros; apply GlobalTheory.sst_isDR <;> assumption)
end

