import Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterProductMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0111

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingSndEmptyBlock
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def tauB (a : Fin 1 → Fin j → ℂ) : Fin j → Fin 1 → ℂ := fun i _ => star (a 0 i)

theorem bC_eq (x : U.RC k j (1 + ρ)) : bC x = tauB (aC x) := by
  funext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  simp [bC, tauB]

theorem tauB_mp : MeasurePreserving (tauB (j := j)) volume volume := by
  have u1 := measurePreserving_funUnique (volume : Measure (Fin j → ℂ)) (Fin 1)
  have u2 : MeasurePreserving (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i))
      volume volume :=
    measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure (Fin 1 → ℂ)))
      (f := fun _ => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm)
      (fun _ => (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1)).symm)
  have h := u2.comp (vconj_mp.comp u1)
  have e : (tauB (j := j)) =
      (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i)) ∘
        (fun v : Fin j → ℂ => star v) ∘ ⇑(MeasurableEquiv.funUnique (Fin 1) (Fin j → ℂ)) := by
    funext a i l
    rfl
  rw [e]; exact h

theorem PsiR_mp : MeasurePreserving (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  have h := ((MeasurePreserving.id (volume : Measure (U.RC k (j + 1) ρ))).prod tauB_mp).comp PsiL_mp
  have e : (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) =
      Prod.map id tauB ∘ (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) := by
    funext z; simp [bC_eq]
  rw [e]; exact h

theorem measurePreserving_snd_empty_block (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (fun η : U.XiH j 0 σ => η.2) volume volume := by
  have h0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h1 : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin j → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h2 : IsProbabilityMeasure (volume : Measure (Fin j → Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi]
    infer_instance
  have h3 : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  exact MeasureTheory.measurePreserving_snd

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def TQ (σ : Equiv.Perm (Fin j)) (p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ) : U.Xi k j 1 ρ σ :=
  ((XC p.2.1.1 p.1.1, XC p.2.1.2 p.1.2), ((aC p.2.1.1, bC p.2.1.2), p.2.2.2))

theorem TQ_mp (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (TQ (k := k) (ρ := ρ) σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ))
      (U.muXi k j 1 ρ σ) := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  set μX := (volume : Measure (U.RC k j (1 + ρ)))
  set μY := (volume : Measure (U.RC k 1 ρ))
  set μH := (volume : Measure (U.XiH j 0 σ))
  set μXC := (volume : Measure (U.RC k (j + 1) ρ))
  set μA := (volume : Measure (Fin 1 → Fin j → ℂ))
  set μB := (volume : Measure (Fin j → Fin 1 → ℂ))
  set μHr := (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ)))
  have s1 := Measure.measurePreserving_swap (μ := μY.prod μY) (ν := (μX.prod μX).prod μH)
  have s2 := measurePreserving_prodAssoc (μX.prod μX) μH (μY.prod μY)
  have s3 := (MeasurePreserving.id (μX.prod μX)).prod (Measure.measurePreserving_swap (μ := μH) (ν := μY.prod μY))
  have s4 := (measurePreserving_prodAssoc (μX.prod μX) (μY.prod μY) μH).symm
  have s5 := (middle_four_swap_measure_preserving μX μX μY μY).prod (MeasurePreserving.id μH)
  have c1 := ((PsiL_mp (k := k) (j := j) (ρ := ρ)).prod (PsiR_mp (k := k) (j := j) (ρ := ρ))).prod (measurePreserving_snd_empty_block σ)
  have t1 := (middle_four_swap_measure_preserving μXC μA μXC μB).prod (MeasurePreserving.id μHr)
  have t2 := measurePreserving_prodAssoc (μXC.prod μXC) (μA.prod μB) μHr
  have h := t2.comp (t1.comp (c1.comp (s5.comp (s4.comp (s3.comp (s2.comp s1))))))
  exact h

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

theorem pointStep : PointStep := by
  intro k j ρ σ d hd c hc zA zA' hzA hzA' E _ _ _ F γ hint
  set Gi : U.Xi k j 1 ρ σ → E := fun ξ => U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ) with hGi
  have hT := TQ_mp (k := k) (ρ := ρ) σ
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  haveI : SigmaFinite ((volume : Measure (U.RC k j (1 + ρ))).prod (volume : Measure (U.RC k j (1 + ρ)))) :=
    inferInstance
  haveI : SFinite (U.muXi k j 0 (1 + ρ) σ) := by
    unfold U.muXi U.muRC U.muXiH; infer_instance
  haveI : SFinite ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
    unfold U.muRC; infer_instance
  have hpt : ∀ p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ, Gi (TQ σ p) =
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := by
    rintro ⟨⟨y, y'⟩, ⟨⟨x, x'⟩, η⟩⟩
    have hgx : D.castM (hs' k j ρ) (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d ((x, x'), η) (fun a => a.elim0)
        ((U.Rn k 1 ρ y)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ y')) =
        U.gaXi (p := j) (s := 1) k ρ σ d ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) (fun _ _ => c) γ :=
      GX σ d hd c hc x x' η y y' γ
    simp only [hGi, TQ]
    rw [PS σ zA zA' hzA hzA' x x' η y y', ← hgx, mul_smul]
    rfl
  have hint' : Integrable (Gi ∘ TQ σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ)) :=
    (hT.integrable_comp hint.aestronglyMeasurable).mpr hint
  show ∫ ξ, Gi ξ ∂(U.muXi k j 1 ρ σ) = _
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)]
  have e2 : (fun p => Gi (TQ σ p)) = fun p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ =>
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := funext hpt
  have hint2 := hint'
  rw [show Gi ∘ TQ σ = fun p => Gi (TQ σ p) from rfl, e2] at hint2
  rw [e2, integral_prod _ hint2]
  congr 1
  funext yy
  dsimp only
  rw [integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MemStepsFull
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma cd_eval (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => eval (vars g) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)
  next p q hp hq =>
    simpa using hp.add hq
  next p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases n with ⟨i, j⟩ | ⟨i, j⟩
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl]
      fun_prop
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]
      have h : ContDiff ℝ ∞ fun g : Mat k r => g i j := by fun_prop
      exact Complex.conjCLE.contDiff.comp h

lemma cd_dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ∞ (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, -, hq⟩ := dminPoly (k := k) z z' l
  have h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cd_gf (z z' : Fin (2 * r + k + 1) → ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  obtain ⟨q, -, hq⟩ := gfPoly (k := k) z z'
  have h : (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cda_invpow {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) {x : Mat k r} (a : ℕ) (h : a = 0 ∨ f x ≠ 0) :
    ContDiffAt ℝ ∞ (fun g => (f g)⁻¹ ^ a) x := by
  rcases h with rfl | h
  · simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  · exact (hf.contDiffAt.inv h).pow a

lemma cda_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma cda_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) {x : Mat k r} (hx : x ∈ V0 D L) : ContDiffAt ℝ ∞ (cvs D e.1) x := by
  obtain ⟨hab, -, -⟩ := he
  have hx0 : 0 < Gf k r D.z D.z' x := hx.1
  have hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0 := fun l hl => Set.mem_iInter₂.1 hx.2 l hl
  have hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG := hx0
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))
    linarith
  have hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0 := fun l hl => by
    rcases hab l hl with hl | rfl
    · exact hxL l hl
    · exact hlast
  have hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0 := fun l => by
    by_cases h : e.1.a l = 0
    · exact Or.inl h
    · exact Or.inr (hnz l (Or.inl h))
  have hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0 := fun l => by
    by_cases h : e.1.b l = 0
    · exact Or.inl h
    · right
      simpa using hnz l (Or.inr h)
  show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x
  refine (cd_eval _).contDiffAt.mul ?_
  refine (cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l *
      (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_
  · exact (cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul
      (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))
  · exact cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))

lemma ckOn_mul {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hA g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hfe'⟩ := hB g₀ hg₀
  refine ⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩
  · exact (hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)
  · intro g hg hgG
    simp only [hfe g hg.1 hgG, hfe' g hg.2 hgG]

lemma ckOn_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) → CkOn ⊤ (GPos D) (C6.Epart fib es) := by
  intro es
  induction es with
  | nil =>
    intro _ g₀ _
    refine ⟨univ, fun _ => 1, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩
    intro g _ _
    simp [C6.Epart]
  | cons e es ih =>
    intro hes
    have h1 := ckOn_Rw_top (hfib e.1) (hes e (by simp))
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    exact ckOn_mul h1 h2

lemma ckOn_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) : CkOn ⊤ (C6.domL D L) (cv D fib e.1) := by
  intro g₀ hg₀
  have hgpos : g₀ ∈ GPos D := domL_gpos hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos
  have hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L) :=
    (isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)
  refine ⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩
  · exact (hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)
  · intro g hg hgG
    simp only [cv, hfe g hg.1 hgG]

def mulCT {nf : ℕ} (t₁ t₂ : CT k r nf) : CT k r nf :=
  ⟨t₁.q * t₂.q, t₁.a + t₂.a, t₁.b + t₂.b, t₁.c + t₂.c, t₁.es ++ t₂.es⟩

lemma cv_mul (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t₁ t₂ : CT k r nf)
    (g : Mat k r) : cv D fib (mulCT t₁ t₂) g = cv D fib t₁ g * cv D fib t₂ g := by
  simp only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply,
    pow_add, Finset.prod_mul_distrib]
  rw [smul_mul_smul_comm]
  congr 1
  ring

lemma good_mul {nf : ℕ} {L : Finset (Fin (r + 2))} {e₁ e : CT k r nf × List (Mat k r)} (h₁ : Good L e₁)
    (h : Good L e) : Good L (mulCT e₁.1 e.1, e.2) := by
  unfold Good at h₁ h ⊢
  obtain ⟨ha1, hs1, -⟩ := h₁
  obtain ⟨ha, hs, hw⟩ := h
  refine ⟨fun l hl => ?_, fun x hx => ?_, hw⟩
  · by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
    · exact ha1 l h1
    · apply ha l
      push_neg at h1
      simpa [mulCT, h1.1, h1.2] using hl
  · simp only [mulCT, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs1 x hx
    · exact hs x hx

def fo {nf : ℕ} (es : List (Fin nf × List (Mat k r))) : ℕ := (es.map fun e => e.2.length).sum

lemma fo_set {nf : ℕ} (X : Mat k r) :
    ∀ (es : List (Fin nf × List (Mat k r))) (i : Fin es.length),
      fo (es.set i ((es.get i).1, X :: (es.get i).2)) = fo es + 1 := by
  intro es
  induction es with
  | nil => intro i; exact i.elim0
  | cons e es ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · simp [fo]
      omega
    · have hj' : j < es.length := by simpa using hj
      have := ih ⟨j, hj'⟩
      have e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) =
          e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2) := rfl
      show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) =
        fo (e :: es) + 1
      rw [e2]
      simp only [fo, List.map_cons, List.sum_cons] at this ⊢
      omega

lemma bound_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) :
    ∀ e' ∈ stepOne D X e, e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + 1 := by
  intro e' he'
  simp only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · rcases ht' with ht' | ht'
    · have hes := dscal_es D X e.1 t' ht'
      refine ⟨?_, by simp [hes]⟩
      simp only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'
      rcases ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl
      · exact (PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)
    · simp only [dfib, List.mem_ofFn] at ht'
      obtain ⟨i, rfl⟩ := ht'
      refine ⟨Nat.le_add_right _ _, ?_⟩
      simp only
      rw [fo_set]; omega
  · refine ⟨Nat.le_add_right _ _, by simp; omega⟩

lemma bound_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by
  intro w
  induction w with
  | nil =>
    intro Lf e' he'
    exact ⟨e', he', by simp, by simp⟩
  | cons X w ih =>
    intro Lf e' he'
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨e, he, hd, ho⟩ := ih Lf e'' he''
    obtain ⟨hd', ho'⟩ := bound_step D X e'' e' he'
    refine ⟨e, he, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      omega

lemma mem_steps_full (D : RealPlaceData k r Wp Wq) {nf : ℕ} (e : CT k r nf × List (Mat k r)) :
    ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w [e] := by
  intro w
  induction w with
  | nil => simp [steps]
  | cons X w ih =>
    simp only [steps, List.foldr_cons, step, List.mem_flatMap, List.cons_append]
    exact ⟨_, ih, by simp [stepOne]⟩

lemma steps_append (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L₁ L₂ : FS k r nf) :
    steps D w (L₁ ++ L₂) = steps D w L₁ ++ steps D w L₂ := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)
    rw [ih]
    simp [step, List.flatMap_append]

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

