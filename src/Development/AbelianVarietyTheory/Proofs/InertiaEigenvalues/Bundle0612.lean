import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0601
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrisms
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

set_option maxHeartbeats 4000000 in

theorem exists_crys_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ sh φ₂ hsh hφC hφsh
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hlp : l.Prime := Fact.out
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps hlK
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps hl1
  have tf1 : ∀ x : ZMod a → K⟦X⟧, (l : ZMod a → K⟦X⟧) * x = 0 → x = 0 := tf_pi hl1
  have tf2 : ∀ x : ZMod a → K⟦X⟧⟦X⟧, (l : ZMod a → K⟦X⟧⟦X⟧) * x = 0 → x = 0 := tf_pi hl2
  have tfS : ∀ x : ↥(Sd t K e), (l : ↥(Sd t K e)) * x = 0 → x = 0 := tf_sub _ tf1
  have tfP : ∀ x : ↥(PPd t K e), (l : ↥(PPd t K e)) * x = 0 → x = 0 := tf_sub _ tf2
  haveI hcS := GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime l a e O K t
  haveI hcP := GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring l a e O K t
  have hSd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t
  have hPd : ∀ F ∈ PPd t K e, F ∈ PPSet t K e := GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t

  let φS : ↥(Sd t K e) →+* ↥(Sd t K e) := (frobTot K a l).toRingHom.restrict (Sd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F hF)).1
  have hφS : ∀ F : ↥(Sd t K e), ∃ B, φS F = F ^ l + (l : ↥(Sd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DS : Delta l ↥(Sd t K e) := Delta.ofLift l φS tfS hφS
  let φP : ↥(PPd t K e) →+* ↥(PPd t K e) := (frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F hF)).1
  have hφP : ∀ F : ↥(PPd t K e), ∃ B, φP F = F ^ l + (l : ↥(PPd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DP : Delta l ↥(PPd t K e) := Delta.ofLift l φP tfP hφP

  let i0 : (Wq l a)⟦X⟧ →+* ↥(Sd t K e) := ((inclS t K).comp (frobS l a)).codRestrict (Sd t K e)
    fun x => Subring.subset_closure (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _)
  let iP0 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((constP a K).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _))
  let iP1 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1
  let dg : ↥(PPd t K e) →+* ↥(Sd t K e) := (diag a K).restrict (PPd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (diag_mem t e (hPd F hF))
  have hdg0 : ∀ x, dg (iP0 x) = i0 x := fun x => Subtype.ext (funext fun τ => constantCoeff_C _)
  obtain ⟨BE, hBE, hE⟩ := GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries l a e O K t
  have hE0 : i0 (eis l a e) = (l : ↥(Sd t K e)) * ⟨BE, Subring.subset_closure hBE⟩ := Subtype.ext hE
  have hEP0 : iP0 (eis l a e) = (l : ↥(PPd t K e)) * ⟨constP a K BE, Subring.subset_closure (constP_mem t e hBE)⟩ :=
    Subtype.ext (by
      change constP a K (inclS t K (frobS l a (eis l a e))) = _
      rw [hE, map_mul, map_natCast]; rfl)
  have hdiff : ∀ x, iP1 x - iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).2
    refine Ideal.mem_span_singleton'.2 ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext ?_⟩
    change B * (l : ZMod a → K⟦X⟧⟦X⟧) = _ - _
    rw [mul_comm]; exact h.symm
  have hmemS : ∀ x ∈ Ideal.span {eis l a e}, i0 x ∈ Ideal.span {(l : ↥(Sd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hE0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP0 : ∀ x ∈ Ideal.span {eis l a e}, iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hEP0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP1 : ∀ x ∈ Ideal.span {eis l a e}, iP1 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    have h := Ideal.add_mem _ (hdiff x) (hmemP0 x hx)
    rwa [sub_add_cancel] at h

  let str0 : ↥(OL (ϖ.field a)) →+* ↥(Sd t K e) ⧸ Ideal.span {(l : ↥(Sd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp i0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemS x hx)).comp (ϖ.strMap a)
  let strP : ↥(OL (ϖ.field a)) →+* ↥(PPd t K e) ⧸ Ideal.span {(l : ↥(PPd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp iP0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemP0 x hx)).comp (ϖ.strMap a)
  let S₀ : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DS (l : ↥(Sd t K e)) (nzd_of_tf tfS)
    (isUnit_delta_l DS tfS) (by rw [sup_idem]; exact hcS) (bdd_self l) str0
  let PP : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DP (l : ↥(PPd t K e)) (nzd_of_tf tfP)
    (isUnit_delta_l DP tfP) (by rw [sup_idem]; exact hcP) (bdd_self l) strP

  have hlift : ∀ r : ↥(OL (ϖ.field a)), ∃ x : (Wq l a)⟦X⟧, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r :=
    fun r => Ideal.Quotient.mk_surjective _
  have hstrP : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → strP r = Ideal.Quotient.mk _ (iP0 x) :=
    fun r x h => by simp only [strP, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]
  have hstr0 : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → str0 r = Ideal.Quotient.mk _ (i0 x) :=
    fun r x h => by simp only [str0, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]

  let p₀ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP0
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP0 fun x => Subtype.ext (funext fun τ => by
        change C (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (C (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφC, frob_toAc])
      f_I := hmemP0
      f_str := fun r x h => (hstrP r x h).symm }
  let p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP1
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP1 fun x => Subtype.ext (funext fun τ => by
        change sh (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (sh (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφsh, frob_toAc])
      f_I := hmemP1
      f_str := fun r x h => by
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) (iP1 x) = strP r
        rw [hstrP r x h, Ideal.Quotient.eq]
        exact hdiff x }
  let δ : GlobalTheory.Prism.Hom PP S₀ :=
    { f := dg
      f_δ := DP.map_δ_of_map_φ DS tfS dg fun y => Subtype.ext (funext fun τ => by
        change constantCoeff (φ₂ (y.1 (τ - 1))) = frob K l (constantCoeff (y.1 (τ - 1)))
        exact constantCoeff_φ₂ sh hsh l φ₂ hφC hφsh _)
      f_I := fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        exact (show ∀ c' : ↥(PPd t K e), dg (c' * (l : ↥(PPd t K e))) ∈ Ideal.span {(l : ↥(Sd t K e))} from
          fun c' => by rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
      f_str := fun r y h => by
        obtain ⟨x, hx⟩ := hlift r
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at h
        rw [hstrP r x hx] at h
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y) = str0 r
        rw [hstr0 r x hx, ← hdg0]
        exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
            Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y') =
            Ideal.Quotient.mk _ (dg (iP0 x)) from fun y' h' => by
          rw [Ideal.Quotient.eq] at h' ⊢
          rw [← map_sub]
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
          rw [← hc, map_mul, map_natCast]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y h }
  let j : ZMod a → ↥(PPd t K e) →+* K⟦X⟧⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ).comp (PPd t K e).subtype
  let j₀ : ZMod a → ↥(Sd t K e) →+* K⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ).comp (Sd t K e).subtype
  have hS1 : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e :=
    fun τ y i => GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t y.1 (hPd _ y.2) τ i
  have hS : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e :=
    fun τ y i => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ HasU.X_mem i) (hS1 τ y i)
  refine ⟨PP, S₀, p₀, p₁, δ, j, j₀, rfl, ?_, fun τ y => rfl, fun τ x => ⟨rfl, rfl⟩, fun τ y => rfl, hS, hS1, ?_⟩
  · exact Hom.ext' (RingHom.ext fun x => Subtype.ext (funext fun τ => by
      change constantCoeff (C (toAc t K (frobS l a x) τ : K⟦X⟧)) = constantCoeff (sh (toAc t K (frobS l a x) τ : K⟦X⟧))
      rw [constantCoeff_C, constantCoeff_sh sh hsh]))
  · intro Cr eC h hCI hCφ hh g
    obtain ⟨E, hEa, hEb, hEc, hEd⟩ := GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor l a e O K t ϖ sh hsh φ₂ hφC hφsh g
    have tfC : ∀ x : Cr.A, (l : Cr.A) * x = 0 → x = 0 := fun x hx => eC.injective (by
      have h1 := congrArg eC hx
      rw [map_mul, map_natCast, map_zero] at h1
      rw [map_zero]; exact acris_nat_cancel hlp.ne_zero h1)
    have hev0 : ∀ x, eC.symm (E (iP0 x)) = h.f ((ϖ.toAinf a).f x) := fun x => eC.injective (by
      rw [RingEquiv.apply_symm_apply]; exact (hEa x _).trans (hh _).symm)
    let ev : GlobalTheory.Prism.Hom PP Cr :=
      { f := eC.symm.toRingHom.comp E
        f_δ := DP.map_δ_of_map_φ Cr.D tfC _ fun y => eC.injective (by
          change eC (eC.symm (E (φP y))) = eC (Cr.D.φ (eC.symm (E y)))
          rw [hCφ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
          exact hEc y.1 y.2 _)
        f_I := fun y hy => by
          rw [hCI]
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
          exact (show ∀ c' : ↥(PPd t K e), eC.symm (E (c' * (l : ↥(PPd t K e)))) ∈ Ideal.span {(l : Cr.A)} from
            fun c' => by
              rw [map_mul, map_mul, map_natCast, map_natCast]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
        f_str := fun r y hy => by
          obtain ⟨x, hx⟩ := hlift r
          change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at hy
          rw [hstrP r x hx] at hy
          have h2 := (h.comp (ϖ.toAinf a)).f_str r x hx
          change Ideal.Quotient.mk Cr.I (h.f ((ϖ.toAinf a).f x)) = Cr.str r at h2
          rw [← h2, ← hev0]
          exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
              Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk Cr.I (eC.symm (E y')) =
              Ideal.Quotient.mk Cr.I (eC.symm (E (iP0 x))) from fun y' h' => by
            rw [Ideal.Quotient.eq] at h' ⊢
            rw [← map_sub, ← map_sub, hCI]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
            rw [← hc, map_mul, map_mul, map_natCast, map_natCast]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y hy }
    refine ⟨ev, Hom.ext' (RingHom.ext fun x => hev0 x), Hom.ext' (RingHom.ext fun x => eC.injective ?_), fun y r => ?_⟩
    · change eC (eC.symm (E (iP1 x))) = eC (h.f ((ainfHom (ϖ.field a) g).f ((ϖ.toAinf a).f x)))
      rw [RingEquiv.apply_symm_apply]
      exact (hEb x _).trans (hh _).symm
    · change ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (eC.symm (E y)) - _
      rw [RingEquiv.apply_symm_apply]
      exact hEd y.1 y.2 (hS · y) r

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDescentDatumAndStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.GalDescent

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] [TameDescentExponentData K l e a]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

def colMat (w : ι → Vec K a ι) : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => Matrix.of fun i j => w j τ i

omit [NeZero e] in

theorem matAct_eq_sum (γ : TameGal K l e a) (w : ι → Vec K a ι) (v : Vec K a ι) :
    Descent.matAct γ (colMat w) v = ∑ j, ringAct γ (fun σ => v σ j) • w j := by
  ext τ i : 2
  simp only [Descent.matAct_apply, colMat, Finset.sum_apply, Pi.smul_apply', ringAct_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem bas_mem_ME (j : ι) : (bas j : Vec K a ι) ∈ ME P := mem_ME_of_mem_M (P.bas_mem_M j)

theorem matAct_mem_ME (γ : TameGal K l e a) (w : ι → ME P) (v : ME P) :
    Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P := by
  rw [matAct_eq_sum]
  exact Submodule.sum_mem _ fun j _ => P.smul_tot_mem_Mext
    (fun τ => (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 v.2 σ j) τ) (w j).2

theorem covers_inv {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ) : Covers K t ϖ h⁻¹ γ⁻¹ := by
  intro f f' hf
  have h1 : galOA O h (ϖ.iTot t K f') = ϖ.iTot t K f := hc f' f fun τ => by
    rw [show (fun σ => ((f' σ : A O K) : K⟦X⟧)) = ringAct γ⁻¹ (fun σ => (f σ : K⟦X⟧)) from funext hf,
      ← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
  apply inclO_injective
  rw [← h1, ← galOW_inclO, ← galOW_inclO, ← galOW_mul, inv_mul_cancel, galOW_one]

theorem toW_sum_smul (c : ι → ZMod a → invE l e (A O K)) (w : ι → ME P)
    (hv : (∑ j, (fun τ => (c j τ : K⟦X⟧)) • (w j).1) ∈ ME P) :
    toW t ϖ P ⟨_, hv⟩ = ∑ j, ϖ.iW t K (c j) • toW t ϖ P (w j) := by
  have : (⟨_, hv⟩ : ME P) = ∑ j, (⟨(fun τ => (c j τ : K⟦X⟧)) • (w j).1,
      P.smul_tot_mem_Mext (fun τ => (c j τ).2) (w j).2⟩ : ME P) := Subtype.ext (by
    rw [Submodule.coe_sum])
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun j _ => toW_smul t ϖ P (c j) (w j) _ fun τ => rfl

theorem act_toW_sum (I : Ident t ϖ P T) {s : GQ l} {g : G} {γ : TameGal K l e a} (hc : Covers K t ϖ s γ)
    (w : ι → ME P) (hw : ∀ j, I.act s g (toW t ϖ P ⟨bas j, bas_mem_ME j⟩) = toW t ϖ P (w j)) (v : ME P)
    (hv : Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P) :
    I.act s g (toW t ϖ P v) = toW t ϖ P ⟨_, hv⟩ := by
  obtain ⟨v, hvm⟩ := v
  let f : ι → ZMod a → invE l e (A O K) := fun j τ => ⟨v τ j, mem_tot.1 hvm τ j⟩
  let f' : ι → ZMod a → invE l e (A O K) := fun j τ =>
    ⟨ringAct γ (fun σ => v σ j) τ, (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 hvm σ j) τ⟩
  have e1 : (∑ j, (fun τ => (f j τ : K⟦X⟧)) • ((⟨bas j, bas_mem_ME j⟩ : ME P) : Vec K a ι)) ∈ ME P := by
    rw [← eq_sum_bas v]; exact hvm
  have e2 : (∑ j, (fun τ => (f' j τ : K⟦X⟧)) • (w j).1) ∈ ME P := by
    rw [← matAct_eq_sum]; exact hv
  have hv1 : toW t ϖ P ⟨v, hvm⟩ = toW t ϖ P ⟨_, e1⟩ := congrArg _ (Subtype.ext (eq_sum_bas v))
  have hv2 : toW t ϖ P ⟨_, hv⟩ = toW t ϖ P ⟨_, e2⟩ := congrArg _ (Subtype.ext (matAct_eq_sum γ _ v))
  rw [hv1, hv2, toW_sum_smul, toW_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Ident.act_smul, hw, UnitModel.galOW_iW_of_covers t ϖ hc (f j) (f' j) fun τ => rfl]

theorem act_eq_of_covers (I : Ident t ϖ P T) (s : G →* GQ l)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    {g g' : G} {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) (hc' : Covers K t ϖ (s g') γ) (v : ME P) :
    I.act (s g) g (toW t ϖ P v) = I.act (s g') g' (toW t ϖ P v) := by
  have h1 : s (g'⁻¹ * g) ∈ ϖ.GfieldInf a := hone _ (by
    rw [map_mul, map_inv, ← inv_mul_cancel γ]
    exact hmul _ _ _ _ (covers_inv hc') hc)
  have h2 : g = g' * (g'⁻¹ * g) := (mul_inv_cancel_left g' g).symm
  rw [h2, map_mul, Ident.act_mul, H1 _ h1]

theorem exists_desc (I : Ident t ϖ P T) (s : G →* GQ l)
    (hex : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    (H2 : ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v : ME P, v.1 ∈ P.M →
      ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (s g) g (toW t ϖ P v) = toW t ϖ P v') :
    ∃ Δ : Descent P, IsGalDesc s I Δ := by
  choose gOf hgOf using hex
  choose w hwM hw using fun γ j => H2 (gOf γ) γ (hgOf γ) ⟨bas j, bas_mem_ME j⟩ (P.bas_mem_M j)
  have hact : ∀ γ (v : ME P), I.act (s (gOf γ)) (gOf γ) (toW t ϖ P v) =
      toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) v⟩ :=
    fun γ v => act_toW_sum I (hgOf γ) (w γ) (hw γ) v _
  have hone' : ∀ j, (w 1 j).1 = bas j := fun j => congrArg Subtype.val (toW_injective t ϖ P
    ((hw 1 j).symm.trans (H1 _ (hone _ (hgOf 1)) _)))
  have hmul' : ∀ γ δ j, (w (γ * δ) j).1 = Descent.matAct γ (colMat fun k => (w γ k).1) (w δ j).1 :=
    fun γ δ j => congrArg Subtype.val (toW_injective t ϖ P (show toW t ϖ P (w (γ * δ) j) =
        toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) (w δ j)⟩ by
      have hc : Covers K t ϖ (s (gOf γ * gOf δ)) (γ * δ) := by
        rw [map_mul]; exact hmul _ _ _ _ (hgOf γ) (hgOf δ)
      rw [← hw, act_eq_of_covers I s hmul hone H1 (hgOf (γ * δ)) hc, map_mul, Ident.act_mul, hw, hact]))
  have hcomm : ∀ γ j, Descent.matAct γ (colMat fun k => (w γ k).1) (P.phi (bas j)) = P.phi (w γ j).1 :=
    fun γ j => by
      have e1 := hact γ ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩
      rw [toW_phi t ϖ P (P.bas_mem_M j), Ident.act_phiW] at e1
      have e2 := toW_phi t ϖ P (hwM γ j)
      have e3 : I.act (s (gOf γ)) (gOf γ) (toW t ϖ P ⟨bas j, mem_ME_of_mem_M (P.bas_mem_M j)⟩) =
          toW t ϖ P ⟨(w γ j).1, mem_ME_of_mem_M (hwM γ j)⟩ := hw γ j
      rw [e3, ← e2] at e1
      exact congrArg Subtype.val (toW_injective t ϖ P e1).symm
  refine ⟨Descent.ofMatrix P (fun γ => colMat fun j => (w γ j).1) (fun γ τ i j => mem_tot.1 (hwM γ j) τ i)
    (fun τ => ?_) (fun γ δ τ => ?_) (fun γ τ => ?_), fun g γ hc v v' hv' => ?_⟩
  · ext i j
    simp only [colMat, Matrix.of_apply, hone', bas, Pi.single_apply, Matrix.one_apply]
  · ext i j
    simp only [colMat, Matrix.of_apply, hmul', Descent.matAct_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.map_apply]
  · refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hcomm γ j) τ) i
    simp only [Descent.matAct_apply, PhiMod.phi_bas, Matrix.col_apply] at this
    simp only [PhiMod.phi_apply, Matrix.mulVec, dotProduct, frobV_apply] at this
    simpa only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply] using this
  · rw [act_eq_of_covers I s hmul hone H1 hc (hgOf γ) v, hact]
    exact congrArg _ (Subtype.ext hv'.symm)

theorem stable_of_desc (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ) {g : G}
    {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  have key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := fun r d => by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    exact congrArg _ (funext fun i => map_mul _ _ _)
  have hcol : ∀ j, inclL t ϖ P (Pi.single j 1) =
      toW t ϖ P ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩ := fun j => by
    rw [toW_of_mx t ϖ P _ (Pi.single j 1) fun τ => ?_, inclL_apply]
    · congr 1
      ext1 j'
      by_cases h : j' = j
      · subst h; simp
      · simp [h]
    · show P.phi (bas j) τ = _
      rw [PhiMod.phi_bas]
      ext1 i
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply]
      rw [Finset.sum_eq_single j (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp)]
      simp
  rintro _ ⟨c, rfl⟩
  rw [pi_eq_sum_univ' c, map_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [key, Ident.act_smul, galOW_inclO, hcol, hΔ g γ hc _ ⟨Δ.act γ (P.phi (bas j)),
    mem_ME_of_mem_L (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))⟩ rfl]
  obtain ⟨c', hc'⟩ := toW_mem_LA t ϖ P (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))
  rw [← hc', ← key]
  exact ⟨_, rfl⟩

theorem stable_of_factor (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ)
    {g g₁ g₂ : G} (hg : g = g₁ * g₂) {γ : TameGal K l e a} (hc : Covers K t ϖ (s g₂) γ)
    (h₁ : ∀ v ∈ LA t ϖ P, I.act (s g₁) g₁ v ∈ LA t ϖ P) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  subst hg
  intro v hv
  rw [map_mul, Ident.act_mul]
  exact h₁ _ (stable_of_desc I s hΔ hc v hv)

end GlobalTheory.BKGal.GalDescent

theorem gal_res_eq {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l} [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι}
    {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T) (x : ↥(GK (ϖ.field a))) (v : ι → OW l ↥(OL LL)) :
    Ident.gal (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) x v =
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v := rfl

theorem coe_inclG {l : ℕ} [Fact l.Prime] (F : FinExt l) (x : ↥(GK F)) : sQ l (inclG F x) = x := rfl

theorem act_mem_LA_of_stable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι} {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T)
    (hst : Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)))
    (x : ↥(GK (ϖ.field a))) : ∀ v ∈ LA (thetaW a LL) ϖ P,
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v ∈ LA (thetaW a LL) ϖ P := fun v hv => by
  have h := (hst x).1 v hv
  rwa [gal_res_eq] at h

open GlobalTheory.BKGal.GalDescent in

theorem GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), (∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v) → (∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v') → (∃ Δ : Descent P, IsGalDesc (sQ l) I Δ) ∧ (Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ g : Gl l, ∀ v ∈ LA (thetaW a LL) ϖ P, I.act (sQ l g) g v ∈ LA (thetaW a LL) ϖ P) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I H1 H2
  obtain ⟨c1, c2, c3, -, c5, c6, -⟩ := GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL
  have hmem : ∀ k : GQ l, k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := fun k => by
    change k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  have hex : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hk⟩ := c3 γ
    exact ⟨⟨k, hmem k⟩, hk⟩
  obtain ⟨Δ, hΔ⟩ := exists_desc I (sQ l) hex c5 (fun k hk => (c6 k).1 hk) H1 H2
  refine ⟨⟨Δ, hΔ⟩, fun hst g => ?_⟩
  choose hOf hhOf kOf hkOf hgOf using c1
  choose γOf hγOf using c2
  have e1 : g = inclG (ϖ.field a) ⟨hOf g, hhOf g⟩ * ⟨kOf g, hmem _⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact (hgOf g).trans (congrArg (· * kOf g) (coe_inclG (ϖ.field a) ⟨hOf g, hhOf g⟩).symm)
  exact stable_of_factor I (sQ l) hΔ e1 (hγOf _ (hkOf g)) (act_mem_LA_of_stable I hst _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.TeichmullerPowerUnit

theorem exists_pow_mul_u_eq_aB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  intro l _ K bk C c hc
  obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt l K bk (c : Om l) hc c.2
  have ho := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w ((l : Om l) ^ n * (c : Om l)) hw
  refine ⟨n, w, ?_⟩
  apply GlobalTheory.Published.FontaineBcris.iotaInj GlobalTheory.T.fontaineBcrisBasicTheorems_proof C
  have hB : C.ι (Per.aB l (wA l bk.a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l bk.a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l bk.a w)
  rw [hB, ← ho, map_mul, map_pow, map_natCast, C.ι_u, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

end GlobalTheory.TeichmullerPowerUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatrStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  first | exact @GlobalTheory.BSP.KisinFF.main | exact GlobalTheory.BSP.KisinFF.main | (intros; apply GlobalTheory.BSP.KisinFF.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLastStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a → ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧ ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  first | exact @GlobalTheory.CuspGeneric.mir_exists_row | exact GlobalTheory.CuspGeneric.mir_exists_row | (intros; apply GlobalTheory.CuspGeneric.mir_exists_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmithFactorizationEtaleOEModPrimePowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smith_factorization_etale_OE_mod_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (P : Matrix (Fin d') (Fin d') (WCb l)), 1 ≤ n → (∀ i j, P i j ∈ bk.OE) → (∃ S : Matrix (Fin d') (Fin d) (WCb l), (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) ↔ ∃ w, v = P *ᵥ w) → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q * R' - Tn) i j) := by
  first | exact @GlobalTheory.SmithQuot.main | exact GlobalTheory.SmithQuot.main | (intros; apply GlobalTheory.SmithQuot.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponentStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_adelicMatrix_localComponent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)), g = h * finGL E a (locGL E a w gw) ∧ ∀ u : GL (Fin a) (w.adicCompletion E), h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  first | exact @GlobalTheory.CuspGeneric.exists_split_loc | exact GlobalTheory.CuspGeneric.exists_split_loc | (intros; apply GlobalTheory.CuspGeneric.exists_split_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rational_conj_mem_boundedCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)), IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  first | exact @GlobalTheory.StabFin.finite_conj_mem | exact GlobalTheory.StabFin.finite_conj_mem | (intros; apply GlobalTheory.StabFin.finite_conj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotentStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  first | exact @GlobalTheory.CuspRep.locTri_adelic | exact GlobalTheory.CuspRep.locTri_adelic | (intros; apply GlobalTheory.CuspRep.locTri_adelic <;> assumption)
end

