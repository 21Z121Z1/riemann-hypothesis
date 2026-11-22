import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIdemDict

open GlobalTheory.AdelicU

variable {D : D7} {v : FinPl D}

theorem exists_eq_splitProj (φ : SplitProj D v) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, φ = splitProj τ := by
  refine ⟨(φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight, ?_⟩
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>

    have hax : a ⊗ₜ[D.host.F] x = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [splitProj_tmul, hax, map_smul, smul_eq_mul]
    rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem isProjAt_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (PP : Formalism.L2.DIV.Pl D.host.E) :
    IsProjAt (D := D) (v := v) (splitProj τ) PP ↔ PP = splitPrime τ := by

  have hred : ∀ x : 𝓞 D.host.E, rdQ (D := D) (v := v) (splitProj τ) (x : D.host.E) = τ x := fun x => by
    simp only [rdQ, splitProj_tmul, one_mul]
  unfold IsProjAt
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [h x, hred, mem_splitPrime]
  · rintro rfl x
    rw [hred, mem_splitPrime]

theorem sigR_compFin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    sigR _ σ (compFin F E v z) = compFin F E v (sigR _ σ z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => simp [sigR, compFin]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem compFin_cA (z : AE D) :
    sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) = compFin D.host.F D.host.E v (cA D z) := by

  have h := sigR_compFin D.sp.cm.sig v z
  exact h

private theorem idem_inl_eq_tensAt_one (D : D7) (v : FinPl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
  rw [Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eq_idem {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {e : AE D} (he : IsIdemOf (D := D) (v := v) (splitProj τ) e) :
    e = GlobalTheory.EmbChart.idem τ := by
  obtain ⟨⟨hee, hce, -⟩, hsum, hone⟩ := he
  have hone' : splitProj τ (compFin D.host.F D.host.E v e) = 1 := hone
  have hε := idem_inl_eq_tensAt_one D v

  have h1 : e = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v e) := by
    calc e = GlobalTheory.EmbChart.tensAt D.host.E v 1 * e := by
          rw [← hε, ← hsum, add_mul, hee, mul_comm (cA D e) e, hce, add_zero]
      _ = _ := by rw [GlobalTheory.EmbChart.tensAt_mul_right, one_mul]
  have hc : cA D e = GlobalTheory.EmbChart.tensAt D.host.E v 1 - e := by
    rw [← hε, ← hsum, add_sub_cancel_left]

  have h2 : compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) τ := by
    apply split_ext (isCMExt_host D) τ
    · rw [splitProj_splitIdem, hone']
    · rw [splitProj_comp_splitIdem, splitProj_comp, compFin_cA, hc, map_sub, GlobalTheory.EmbChart.compFin_tensAt,
        map_sub, map_one, hone', sub_self]
  rw [h1, h2]
  rfl

private theorem eq_of_isIdemAt_of_isIdemAt' {e : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem exists_emb {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP) :
    ∃ (v : FinPl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), IsIdemOf (D := D) (v := v) (splitProj τ) e ∧ PP = splitPrime τ := by
  obtain ⟨⟨hee, hce, w, ε, ⟨α, rfl, hαw, hαo⟩, hsum⟩, -⟩ := id he

  have hα : α = singleV D.host.F w 1 := by
    classical
    apply RestrictedProduct.ext
    intro u
    by_cases hu : u = w
    · subst hu
      rw [singleV, RestrictedProduct.single_eq_same]
      exact hαw
    · rw [singleV, RestrictedProduct.single_eq_of_ne _ _ hu]
      exact hαo u hu
  subst hα
  have hsum' : e + cA D e = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl w) := hsum
  have hε := idem_inl_eq_tensAt_one D w

  set y := compFin D.host.F D.host.E w e with hy
  have hy1 : y * y = y := by rw [hy, ← map_mul, hee]
  have hy2 : y + sigR _ D.sp.cm.sig y = 1 := by
    rw [hy, compFin_cA, ← map_add, hsum', hε, GlobalTheory.EmbChart.compFin_tensAt]
  have hσy : sigR _ D.sp.cm.sig y = 1 - y := eq_sub_of_add_eq' hy2

  have hnf : ¬ IsField (Fv D.host.F w ⊗[D.host.F] D.host.E) := by
    intro hf
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, add_zero] at hy2
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, ← hy2, mul_zero, mul_zero])
    · obtain ⟨z, hz⟩ := hf.mul_inv_cancel hy0
      have hy1' : y = 1 := by
        calc y = y * (y * z) := by rw [hz, mul_one]
          _ = y * y * z := by rw [mul_assoc]
          _ = 1 := by rw [hy1, hz]
      rw [hy1', map_one] at hy2
      have h10 : (1 : Fv D.host.F w ⊗[D.host.F] D.host.E) = 0 := add_left_cancel (hy2.trans (add_zero 1).symm)
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  have hfin : Module.finrank (Fv D.host.F w) (Fv D.host.F w ⊗[D.host.F] D.host.E) = 2 := by
    rw [Module.finrank_baseChange]
    exact (isCMExt_host D).2.2.1
  obtain ⟨φ₀⟩ := nonempty_algHom_of_not_isField hfin hnf
  obtain ⟨τ₀, rfl⟩ := exists_eq_splitProj (D := D) (v := w) φ₀

  have hτ : ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F w, splitProj τ y = 1 := by
    have hp : IsIdempotentElem (splitProj τ₀ y) := by
      unfold IsIdempotentElem
      rw [← map_mul, hy1]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hp with h0 | h1
    · refine ⟨τ₀.comp D.sp.cm.sig, ?_⟩
      rw [splitProj_comp, hσy, map_sub, map_one, h0, sub_zero]
    · exact ⟨τ₀, h1⟩
  obtain ⟨τ, hτ⟩ := hτ
  have hi : IsIdemOf (D := D) (v := w) (splitProj τ) e := ⟨he.1, hsum', hτ⟩
  refine ⟨w, τ, hi, ?_⟩

  have he' := he
  rw [eq_idem hi] at he'
  exact eq_of_isIdemAt_of_isIdemAt' he' (GlobalTheory.EmbChart.isIdemAt_idem τ)

theorem idem_dictionary : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  intro D
  refine ⟨fun e PP he => ?_, fun v φ PP hφ => ?_⟩
  · obtain ⟨w, τ, hi, rfl⟩ := exists_emb he
    exact ⟨w, splitProj τ, hi, (isProjAt_iff τ _).2 rfl⟩
  · obtain ⟨τ, rfl⟩ := exists_eq_splitProj φ
    obtain rfl : PP = splitPrime τ := (isProjAt_iff τ PP).1 hφ
    refine ⟨(splitPrime_liesOver τ).over.symm, fun PP' h' => (isProjAt_iff τ PP').1 h', fun e he => ?_⟩
    obtain rfl := eq_idem he
    refine ⟨GlobalTheory.EmbChart.isIdemAt_idem τ, fun e' he' => ?_, fun φ' hφ' => ?_⟩
    ·
      obtain ⟨w, τ', hi', hP'⟩ := exists_emb he'
      have hw : w = v := by
        calc w = (splitPrime τ').under (𝓞 D.host.F) := (splitPrime_under τ').symm
          _ = (splitPrime τ).under (𝓞 D.host.F) := by rw [hP']
          _ = v := splitPrime_under τ
      subst hw
      rw [eq_idem hi', splitPrime_injective (isCMExt_host D) hP'.symm]
    ·
      obtain ⟨τ'', rfl⟩ := exists_eq_splitProj φ'
      have h2 := GlobalTheory.EmbChart.isIdemAt_idem τ''
      rw [← eq_idem hφ'] at h2
      rw [splitPrime_injective (isCMExt_host D) (eq_of_isIdemAt_of_isIdemAt' h2 (GlobalTheory.EmbChart.isIdemAt_idem τ))]

end GlobalTheory.SplitIdemDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitProjChart

variable {D : D7} {v : FinPl D}

def emb (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem emb_apply (φ : SplitProj D v) (x : D.host.E) : emb φ x = rdQ φ x := rfl

theorem splitProj_emb (φ : SplitProj D v) : GlobalTheory.AdelicU.splitProj (emb φ) = φ := by
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [GlobalTheory.AdelicU.splitProj_tmul, emb_apply, rdQ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]

theorem chart_idem (φ : SplitProj D v) : GlobalTheory.SplitHecke.Chart (GlobalTheory.EmbChart.idem (emb φ)) v (rdA φ) := by
  have h := GlobalTheory.EmbChart.chart_idem (emb φ)
  rw [splitProj_emb] at h
  exact h

theorem rdA_idem (φ : SplitProj D v) : rdA φ (GlobalTheory.EmbChart.idem (emb φ)) = 1 := by
  change φ (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (GlobalTheory.EmbChart.idem (emb φ))) = 1
  rw [GlobalTheory.EmbChart.compFin_idem]
  nth_rewrite 1 [← splitProj_emb φ]
  exact GlobalTheory.AdelicU.splitProj_splitIdem _ _

theorem eq_idem {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : e = GlobalTheory.EmbChart.idem (emb φ) := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he.1 (GlobalTheory.EmbChart.isSplitIdem_idem _)).resolve_right fun h => ?_
  have := congrArg (rdA φ) h
  rw [map_mul, he.2.2, rdA_idem, map_zero, mul_one] at this
  exact one_ne_zero this

theorem rdE_toEAf (φ : SplitProj D v) (a : AE D) : rdE φ (toEAf D a) = rdA φ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem rdA_incA (φ : SplitProj D v) (x : D.host.E) : rdA φ (incA D x) = rdQ φ x := by
  change φ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one]; rfl

theorem continuous_rdA (φ : SplitProj D v) : Continuous (rdA φ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (rdA φ) ?_
  have h1 : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact h1.congr fun y => ((chart_idem φ).2.2.1 y).symm

theorem chart_rdA : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e :=
  fun _ _ φ _ he => ⟨eq_idem he ▸ chart_idem φ, rdE_toEAf φ, rdA_incA φ, continuous_rdA φ,
    fun _ he' => (eq_idem he').trans (eq_idem he).symm⟩

end GlobalTheory.SplitProjChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.RadRev

open Matrix

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.mp hij) with hlt | heq
    · have hne : i ≠ j := fun hh => (ne_of_lt hlt) (by rw [hh])
      rw [hP i j hlt, Matrix.one_apply_ne hne]
    · obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at heq
      subst heq
      rw [hD]
      by_cases hs : i' = j'
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]
  · intro H
    refine ⟨fun i j hji => ?_, fun a i j => ?_⟩
    · have hne : i ≠ j := fun hh => (ne_of_lt hji) (by rw [hh])
      rw [H i j (not_lt.mpr hji.le), Matrix.one_apply_ne hne]
    · rw [H _ _ (by simp)]
      by_cases hs : i = j
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [∀ a, Fintype (m' a)]
  [∀ a, DecidableEq (m' a)] in

theorem blk_lt_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') {i j : n} (hij : blk e' j < blk e' i) : blk e j < blk e i := by
  have hne : i ≠ j := fun hh => (ne_of_lt hij) (by rw [hh])
  by_contra hc
  have hdet : IsUnit (Matrix.transvection i j (1 : R)).det := by
    rw [Matrix.det_transvection_of_ne _ _ hne]
    exact isUnit_one
  obtain ⟨t, ht⟩ : ∃ t : GL n R, (t : Matrix n n R) = Matrix.transvection i j (1 : R) :=
    ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩
  have hent : ∀ k l, (t : Matrix n n R) k l = (1 : Matrix n n R) k l + if i = k ∧ j = l then 1 else 0 := by
    intro k l
    rw [ht]
    simp [Matrix.transvection, Matrix.single_apply]
  have hmem : t ∈ parab R e := by
    rw [mem_parab]
    intro k l hkl
    have hkl' : k ≠ l := fun hh => (ne_of_lt hkl) (by rw [hh])
    rw [hent, Matrix.one_apply_ne hkl', zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hc hkl
  have hzero := mem_parab.mp (h hmem) i j hij
  rw [hent, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩] at hzero
  exact one_ne_zero hzero

theorem unipRad_le_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') : unipRad R e' ≤ unipRad R e := by
  intro g hg
  rw [mem_unipRad_entries] at hg ⊢
  intro i j hij
  exact hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))

theorem stdMaxRad_le_unipRad : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  intro F _ r a b s h d hd hle
  exact unipRad_le_of_parab_le hle

end GlobalTheory.RadRev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLaw

variable {D : D7}

theorem isRes_one_of_unrAt (χ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro ha
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (((k : D.host.E)) : PP.adicCompletion D.host.E) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
    exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 ha
  exact (h _ hv).symm

theorem natCast_mem_of_isConjPl {PP PP' : Pl D.host.E} (h : IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c, hc, hc'⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc']
    simp
  exact this ▸ hc

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_prime_mem_of_isTwistPlaces {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem_of_div {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem TameOn.mul {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c c' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P c') :
    TameOn (χ * χ') e P (fun PP => c PP * c' PP) := by
  intro x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, Circle.coe_mul, h x h1 hx h2 h3 u hu, h' x h1 hx h2 h3 u hu, ← Finset.prod_mul_distrib]
  simp

theorem TameOn.mul_inv_one {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P fun _ => 1) :
    TameOn (χ * χ'⁻¹) e P c := by
  intro x h1 hx h2 h3 u hu
  have h4 := h' x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, h x h1 hx h2 h3 u hu, h4]
  simp

theorem tameOn_step : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ ∀ (e : AE D) (P : Finset (Pl D.host.E)), (∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) → IsIdemSum e P → TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) ∧ TameOn (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) e P (resChr L t ((j : ℕ) + 1)) := by
  classical
  intro D T0 L μ0 hL t j

  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) (natCast_mem_of_isConjPl hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem_of_div hk)
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun e P hP he => ?_⟩
  have hM := L.C.isMu0 j
  have t1 : TameOn (L.mu0 ((j : ℕ) + 1)) e P (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.C.mu0 j) e P _ (hL.mu0 j) hM.tame he ?_ ?_
    · intro PP h1 h2
      refine hM.unr PP fun k hk => ?_
      rcases GlobalTheory.T.place_over_typePrime_divides_or_conjugate D L.C.P k PP hk with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inl ((hL.Pg PP).2 ⟨k, h⟩)))
      · exact h2 ⟨PP', (hP PP').2 (Or.inl ((hL.Pg PP').2 ⟨k, h⟩)), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact hL.chi j PP hg
      · simp only [if_neg hg]
        have hQ := ((hP PP).1 h).resolve_left hg
        exact isRes_one_of_unrAt _ _ (hM.unr PP fun k hk => (hoff k PP hk).1 hQ)
  have t2 : TameOn (L.xi t) e P (fun PP => if PP ∈ L.Pg then 1 else L.xiR t PP) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.xiH t) e P _ (hL.xi t) (hL.xi_tame t) he ?_ ?_
    · intro PP h1 h2
      by_contra hn
      rcases (hL.Q_ram t PP).1 hn with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inr h))
      · exact h2 ⟨PP', (hP PP').2 (Or.inr h), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        refine isRes_one_of_unrAt _ _ ?_
        by_contra hn
        rcases (hL.Q_ram t PP).1 hn with h | h
        · exact (hPg PP hg).1 h
        · exact (hPg PP hg).2 h
      · simp only [if_neg hg]
        exact hL.xiR t PP (((hP PP).1 h).resolve_left hg)
  have t3 : TameOn L.eta e P (fun _ => 1) :=
    GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ L.C.eta e P _ hL.eta (fun PP x hx _ => L.C.isEta.unr PP x hx) he
      (fun PP _ _ => L.C.isEta.unr PP) (fun PP _ => isRes_one_of_unrAt _ _ (L.C.isEta.unr PP))
  have t4 : TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) := by
    have h := t1.mul t2
    have hc : (fun PP => (if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) *
        (if PP ∈ L.Pg then 1 else L.xiR t PP)) = resChr L t ((j : ℕ) + 1) := by
      funext PP
      unfold resChr
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg, mul_one]
      · simp only [if_neg hg, one_mul]
    rw [hc] at h
    exact h
  exact ⟨t4, t4.mul_inv_one t3⟩

end GlobalTheory.StepLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTwistDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  first | exact @GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | exact GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | (intros; apply GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc <;> assumption)
end

