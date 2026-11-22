import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegFlFlagMapRenamePerm
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.Schubert

theorem degFl_rename_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (ρ : ι → Equiv.Perm (Fin N))
    (P : MvPolynomial (ι × Fin N) ℝ) :
    Formalism.DegreeFormula.degFl ι N (rename (fun x : ι × Fin N => (x.1, ρ x.1 x.2)) P) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * Formalism.DegreeFormula.degFl ι N P := by
  set f : ι × Fin N → ι × Fin N := fun x => (x.1, ρ x.1 x.2) with hfdef
  have hinj : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [(ρ a).injective h2]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, j⟩
    exact ⟨(a, (ρ a).symm j), by simp [hfdef]⟩
  have hexp : ∀ σ : ι → Equiv.Perm (Fin N),
      Formalism.DegreeFormula.permExp (σ * ρ⁻¹) = (Formalism.DegreeFormula.permExp σ).mapDomain f := by
    intro σ
    ext y
    obtain ⟨⟨a, i⟩, rfl⟩ := hsurj y
    rw [Finsupp.mapDomain_apply hinj]
    simp [Formalism.DegreeFormula.permExp, hfdef, Pi.mul_apply, Pi.inv_apply]
  have hsgn : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign ((σ * ρ⁻¹) τ) : ℤ) : ℝ)) =
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Pi.mul_apply, Pi.inv_apply, Equiv.Perm.sign_inv]
  have key : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        (rename f P).coeff (Formalism.DegreeFormula.permExp σ) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * ∑ σ : ι → Equiv.Perm (Fin N),
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (Formalism.DegreeFormula.permExp σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (ρ⁻¹ : ι → Equiv.Perm (Fin N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.coe_mulRight, hsgn, hexp, coeff_rename_mapDomain _ hinj]
    ring
  unfold Formalism.DegreeFormula.degFl
  rw [key]
  ring

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perm_val_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) (i : ℕ) (h1 : i < Dw.mult a) (h2 : i < Dw.mult b) :
    ((w a ⟨i, h1⟩ : Fin (Dw.mult a)) : ℕ) = ((w b ⟨i, h2⟩ : Fin (Dw.mult b)) : ℕ) := by
  subst e; rfl

theorem sign_perm_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) : Equiv.Perm.sign (w a) = Equiv.Perm.sign (w b) := by
  subst e; rfl

def flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm (Fin (Dw.p + Dw.q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr
    ((finCongr (GlobalTheory.PointChern.mult_of_mem Dw τ.2)).permCongr (w τ.1))
    (Fin.revPerm.permCongr ((finCongr (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ))).permCongr
      (w (conjEmb τ.1)))))

theorem sign_flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm.sign (flagPerm Dw w τ) = Equiv.Perm.sign (w τ.1) * Equiv.Perm.sign (w (conjEmb τ.1)) := by
  simp only [flagPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem flagPerm_big {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    ((flagPerm Dw w τ ⟨i, hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) = ((w τ.1 i : Fin (Dw.mult τ.1)) : ℕ) := by
  have hp : (i : ℕ) < Dw.p := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw τ.2; omega
  have e : (⟨i, hi⟩ : Fin (Dw.p + Dw.q)) = Fin.castAdd Dw.q ⟨i, hp⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd, Equiv.permCongr_apply]
  simp

theorem flagPerm_small {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) {σ : E →+* ℂ}
    (hσ : ¬ σ (H.rt : E) = H.rt0) (i : Fin (Dw.mult σ)) (hi : Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p + Dw.q) :
    ((flagPerm Dw w ⟨conjEmb σ, GlobalTheory.AllWt.conj_mem hσ⟩ ⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) =
      Dw.p + (Dw.q - 1 - ((w σ i : Fin (Dw.mult σ)) : ℕ)) := by
  have hq : (i : ℕ) < Dw.q := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw hσ; omega
  have e : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p ⟨Dw.q - 1 - i, by omega⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, finCongr_apply, finCongr_symm, Fin.coe_cast]
  have key : ∀ x : Fin (Dw.mult (conjEmb (conjEmb σ))), (x : ℕ) = (i : ℕ) →
      ((w (conjEmb (conjEmb σ)) x : Fin _) : ℕ) = ((w σ i : Fin (Dw.mult σ)) : ℕ) := by
    rintro ⟨x, hx⟩ hxi
    simp only at hxi
    subst hxi
    exact perm_val_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb σ) _ _ i.2
  rw [key _ (by simp; omega)]
  omega

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagMap_rename {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    flagMap Dw (rename (fun x : GlobalTheory.GoodMetric.Root Dw.mult =>
        (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q) =
      rename (fun x : GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) => (x.1, flagPerm Dw w x.1 x.2)) (flagMap Dw Q) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun x => ?_
  simp only [AlgHom.comp_apply, rename_X, flagMap, aeval_X]
  obtain ⟨σ, i⟩ := x
  by_cases h : σ (H.rt : E) = H.rt0
  · simp only [flagRoot, dif_pos h, rename_X]
    congr 2
    exact Fin.ext (flagPerm_big Dw w ⟨σ, h⟩ i _).symm
  · simp only [flagRoot, dif_neg h, map_neg, rename_X]
    congr 3
    exact Fin.ext (flagPerm_small Dw w h i _).symm

theorem prod_sign_eq {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) :
    (∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) = ∏ τ : GlobalTheory.AllWt.Psi H, Equiv.Perm.sign (flagPerm Dw w τ) := by
  simp only [sign_flagPerm, Finset.prod_mul_distrib]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  refine Fintype.prod_equiv
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) } _ _ ?_
  intro τ
  simp only [Equiv.coe_fn_mk]
  exact sign_perm_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb τ.1).symm

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

theorem degFl_flagMap_rename_perm (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw (MvPolynomial.rename
              (fun x : GlobalTheory.GoodMetric.Root Dw.mult => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q)) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) *
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
  rw [flagMap_rename, degFl_rename_perm, prod_sign_eq]
  push_cast
  rfl

end GlobalTheory.Schubert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigAdOfRowEig
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

theorem eigAd_of_rowEig : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, (∀ (i : Fin (Dof x).R.m) (σ : (Dof x).what₂.FT) (k : ℕ) (Pl : PlE (Dof x).host) α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr → (Dof x).nd.goodRow σ → (Dof x).what₂.isot (i.1 + 1) σ ≠ ⊥ → (Dof x).what₂.embLL (eig (i.1 + 1) σ k Pl : (Dof x).what₂.LL) = hkNorm x.m.z.R i k Pl * GlobalTheory.EigRows.rowEig x.r.Y i σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) → EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ eig heig => ?_
  intro i σ k Pl α Rr hd hσ y hy
  by_cases h0 : (Dof x).what₂.isot (i.1 + 1) σ = ⊥
  · rw [h0, Submodule.mem_bot] at hy
    subst hy
    simp
  · have e1 := heig i σ k Pl α Rr hd hσ h0
    have hP := (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)).offPg x.m.z.lev.is hd.offS
    have e2 := GlobalTheory.EigRows.heckeOn_partR x.r.Y x.m.z.lev.is i hP hd.le hd.elt hd.reps σ
      ((GlobalTheory.EigRows.mem_isot_iff x.r.Y i σ y).1 hy)
    change hkNorm x.m.z.R i k Pl • Mult.heckeOn _ Rr (GlobalTheory.EigRows.readW x.r.Y i y) = _ • GlobalTheory.EigRows.readW x.r.Y i y
    rw [e2, e1, smul_smul]

end GlobalTheory.HeightCounting.RatSide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricGramSmoothInFamilyFrames
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LieBase.GramSmooth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts p σ}

theorem cInfAt_mul {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sub {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z - g z) y :=
  hf.comp₂ hg (G := fun x => x.1 - x.2) (contDiff_fst.sub contDiff_snd)

def CxInf (f : GlobalTheory.CxPts p σ → ℂ) (y : GlobalTheory.CxPts p σ) : Prop :=
  CInfAt (fun z => (f z).re) y ∧ CInfAt (fun z => (f z).im) y

variable {f g : GlobalTheory.CxPts p σ → ℂ}

theorem CxInf.mul (hf : CxInf f y) (hg : CxInf g y) : CxInf (fun z => f z * g z) y := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re]; exact cInfAt_sub (cInfAt_mul hf.1 hg.1) (cInfAt_mul hf.2 hg.2)
  · simp only [Complex.mul_im]; exact (cInfAt_mul hf.1 hg.2).add (cInfAt_mul hf.2 hg.1)

theorem CxInf.star (hf : CxInf f y) : CxInf (fun z => star (f z)) y := by
  refine ⟨?_, ?_⟩
  · simpa [Complex.star_def] using hf.1
  · simpa [Complex.star_def] using hf.2.neg

theorem CxInf.sum {κ : Type} (s : Finset κ) {f : κ → GlobalTheory.CxPts p σ → ℂ} (h : ∀ a ∈ s, CxInf (f a) y) :
    CxInf (fun z => ∑ a ∈ s, f a z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_⟩ <;> simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_insert ha, Complex.add_re]; exact h1.1.add h2.1
    · simp only [Finset.sum_insert ha, Complex.add_im]; exact h1.2.add h2.2

theorem cxInf_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : GlobalTheory.CxPts X.str σ} {f : X.Fn}
    (hf : RegAt (under y) f) : CxInf (fun z => ratVal f z) y :=
  ⟨GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
               (G := fun v => (v ()).re) (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ ())),
    GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
      (G := fun v => (v ()).im) (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ ()))⟩

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem cInfAt_comp {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'}
    {σ : k →+* ℂ} {σ' : k' →+* ℂ} {π : Y' ⟶ Y} {m : GlobalTheory.CxPts p' σ' → GlobalTheory.CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ π)
    {f : GlobalTheory.CxPts p σ → ℝ} {z : GlobalTheory.CxPts p' σ'} (h : CInfAt f (m z)) : CInfAt (fun w => f (m w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, (mem_ptsIn_preimage hm).2 h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_of_comp hm] using h₃
  · simp only [← ev_of_comp hm]
    exact (continuous_of_comp hm).continuousAt.eventually h₅

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem eventually_mem : ∀ (F : Type) [Field F] (X : Var F) (σ : F →+* ℂ) (ι : Type) [Finite ι] (m : ι → ℕ) (S : Fr (ratOf X) m 0) (y : GlobalTheory.CxPts X.str σ) (A : Mat m X.Fn), A ∈ S.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  intro F _ X σ ι _ m S y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem gram_entry_cInfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ (τ : E →+* ℂ) (p q : Fin (Dw.mult τ)) (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) → cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 → ∃ h : GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → ℂ, CInfAt (fun z => (h z).re) y ∧ CInfAt (fun z => (h z).im) y ∧ ∀ᶠ z in 𝓝 y, ∀ (hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z)), Φ.IsMap (evHom hz) f → G.gram (cxOf e σ hj z) f τ p q = h z := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j hj V φ Φ hφ τ p q y hy hyV
  obtain ⟨g, hre, him, hg⟩ := hG V φ Φ τ p q hφ
  have hT : IsOpen ({y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1) := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hm : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), (cxOf e σ hj z).1 = z.1 ≫ j := fun _ => rfl
  have hyT : cxOf e σ hj y ∈ {y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1 :=
    ⟨mem_ptsIn.1 ((mem_ptsIn_preimage hm).1 hy), hyV⟩
  have cre := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 hre _ hyT
  have cim := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 him _ hyT
  refine ⟨fun z => g (cxOf e σ hj z), GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cre,
    GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cim, ?_⟩
  filter_upwards [(continuous_of_comp hm).continuousAt.preimage_mem_nhds (hT.mem_nhds hyT)] with z hz hz' f hf
  exact hg _ hz.1 hz' f hf

end GlobalTheory.LieBase.GramSmooth

theorem GlobalTheory.LieBase.cInfAt_gramOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j f₀ S A₀ hj hoi hT y hy A hA τ a b
  obtain ⟨U, hU, φ, Φ, hzU, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 := mem_ptsIn.2 hzU
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β Z σ F e X j f₀ S A₀ hj hoi hT V φ Φ hφ' A
  choose h hre him hev using fun p q => GlobalTheory.LieBase.GramSmooth.gram_entry_cInfAt E H Dw l Xo c O β Z σ G hG F e X j hj V φ Φ hφ' τ p q y hy hyV
  have hS := GlobalTheory.LieBase.GramSmooth.eventually_mem F X (σ.comp e.toRingHom) (E →+* ℂ) Dw.mult S y A hA
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have hall := Filter.eventually_all.2 fun pq : Fin (Dw.mult τ) × Fin (Dw.mult τ) => hev pq.1 pq.2
  have hreg := (hM y hA hyV).1 τ
  have key : ∀ᶠ z in 𝓝 y, gramOf e G hj f₀ A₀ A z τ a b =
      ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z := by
    filter_upwards [hS, hVn, hall] with z hzS hzV hzall
    obtain ⟨-, hex, hco⟩ := hM z hzS hzV
    have hov : σ = (evHom hzV).comp φ := GlobalTheory.ShFam.EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [gramOf, dif_pos hex]
    show (G.gram (cxOf e σ hj z) hex.choose τ)ᵀ a b = _
    rw [Matrix.transpose_apply, G.change (cxOf e σ hj z) f, hco _ hex.choose_spec f hf τ]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hzall (p, q) hzV f hf]
  open GlobalTheory.LieBase.GramSmooth in
  have hC : CxInf (fun z => ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z) y :=
    CxInf.sum _ fun q _ => (CxInf.sum _ fun p _ => (cxInf_ratVal (hreg p b)).star.mul ⟨hre p q, him p q⟩).mul
      (cxInf_ratVal (hreg q a))
  exact ⟨hC.1.congr (key.mono fun z hz => congrArg Complex.re hz), hC.2.congr (key.mono fun z hz => congrArg Complex.im hz)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_span_inclusion_injective : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  first | exact @GlobalTheory.EigSpanDesc.iotaR_injective_states | exact GlobalTheory.EigSpanDesc.iotaR_injective_states | (intros; apply GlobalTheory.EigSpanDesc.iotaR_injective_states <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Descent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy

theorem GlobalTheory.HeightCounting.Up.hkCopyRestaged : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : LI hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∃ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) := by
  intro _ _ hL K B' f' T' w' _ _ _ B f T w _ _ _ _ _ _ _ P x lb P' _ x' l' _ N ι e hN x'' l'' ho _ _ _ _ _ _ _ _
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  have hS : GlobalTheory.TwistChoice.SameExport (Dof x) (Dof x'') := hD ▸ hN.cp.toSameExport
  exact GlobalTheory.HeightCounting.Up.HkCopy.exists_cHk_copy hS lb.b.Bs.cHk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRayStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | exact GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | (intros; apply GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinctStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_auxiliary_places_split_distinct : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  first | exact @GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | exact GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | (intros; apply GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoicesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) := by
  first | exact @GlobalTheory.Mem.HypCMRec.hypCM_at_record | exact GlobalTheory.Mem.HypCMRec.hypCM_at_record | (intros; apply GlobalTheory.Mem.HypCMRec.hypCM_at_record <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrdeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  first | exact @GlobalTheory.HeightCounting.Up.rootsLL_evLgG | exact GlobalTheory.HeightCounting.Up.rootsLL_evLgG | (intros; apply GlobalTheory.HeightCounting.Up.rootsLL_evLgG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadratStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) := by
  first | exact @GlobalTheory.Mem.HostEFK.hypEFK_ev | exact GlobalTheory.Mem.HostEFK.hypEFK_ev | (intros; apply GlobalTheory.Mem.HostEFK.hypEFK_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoicesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  first | exact @GlobalTheory.Mem.RankSize.rank_ge_hundred | exact GlobalTheory.Mem.RankSize.rank_ge_hundred | (intros; apply GlobalTheory.Mem.RankSize.rank_ge_hundred <;> assumption)
end

