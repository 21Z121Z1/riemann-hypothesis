import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ShFam.InterpSmooth

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {U : Set E'}

theorem contDiffOn_iff_re_im {f : E' → ℂ} : ContDiffOn ℝ ∞ f U ↔
    ContDiffOn ℝ ∞ (fun v => (f v).re) U ∧ ContDiffOn ℝ ∞ (fun v => (f v).im) U := by
  refine ⟨fun h => ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩, fun h => ?_⟩
  have := (Complex.ofRealCLM.contDiff.comp_contDiffOn h.1).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h.2).mul (contDiffOn_const (c := Complex.I)))
  refine this.congr fun v _ => ?_
  simp [Complex.re_add_im]

variable {n : ℕ}

def EntSm (A : E' → Matrix (Fin n) (Fin n) ℂ) (U : Set E') : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun v => A v a b) U

theorem det_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) : ContDiffOn ℝ ∞ (fun v => (A v).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem inv_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) (h0 : ∀ v ∈ U, (A v).det ≠ 0) :
    EntSm (fun v => (A v)⁻¹) U := by
  intro a b
  have hadj : ContDiffOn ℝ ∞ (fun v => (A v).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    refine det_sm (A := fun v => (A v).updateRow b (Pi.single a 1)) fun i k => ?_
    by_cases hi : i = b
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact h _ _
  refine (((det_sm h).inv h0).mul hadj).congr fun v _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Pi.inv_apply]

theorem mix_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) : EntSm (fun v => mix (s v) (A v) (B v)) U := fun a b => by
  have hs' : ContDiffOn ℝ ∞ (fun v => ((s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  have h1 : ContDiffOn ℝ ∞ (fun v => ((1 - s v : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
  refine ((h1.mul (hA a b)).add (hs'.mul (hB a b))).congr fun v _ => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem dual_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hp : ∀ v ∈ U, (A v).PosDef) :
    EntSm (fun v => dualGram (A v)) U :=
  fun a b => (inv_sm hA (fun v hv => (hp v hv).det_pos.ne') b a).congr fun _ _ => rfl

theorem mixDual_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) (hpA : ∀ v ∈ U, (A v).PosDef) (hpB : ∀ v ∈ U, (B v).PosDef)
    (hs01 : ∀ v ∈ U, s v ∈ Set.Icc (0 : ℝ) 1) : EntSm (fun v => mixDual (s v) (A v) (B v)) U :=
  dual_sm (mix_sm hs (dual_sm hA hpA) (dual_sm hB hpB)) fun v hv =>
    mix_posDef (hs01 v hv) (dualGram_posDef (hpA v hv)) (dualGram_posDef (hpB v hv))

theorem ite_sm {c : Prop} [Decidable c] {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hB : EntSm B U) :
    EntSm (fun v => if c then A v else B v) U := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact hA
  · simp only [hc, ↓reduceIte]; exact hB

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.ShFam.InterpSmooth

namespace GlobalTheory.ShFam

open InterpSmooth

theorem ToroidalCompactificationData.smoothOn_eigMetAt_some : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ)
    (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R →
    (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} →
    (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  intro D A N j S κ s x σ R hR hH V φ F τ a b hφ
  classical
  set P := ptsIn (genStr s.T.Z) σ V.1 with hP
  set Bc := {y : CxPts (genStr s.T.Z) σ | ¬ LiesIn y (genBd s.T.Z)} with hBc
  have hBo : IsOpen Bc := isOpen_not_liesIn _

  have hphi : ∀ y (hy : y ∈ P), σ = (evHom hy).comp φ := fun y hy => by
    have e : spMap σ = spMap ((evHom hy).comp φ) := by
      rw [← y.2, ← spMap_evHom hy, Category.assoc, hφ, ← Spec.map_comp]; rfl
    exact spMap_inj e
  have hfr : ∀ y (hy : y ∈ P), ∃ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), F.IsMap (evHom hy) f := fun y hy =>
    F.exists_isMap (evHom hy) (hphi y hy) (by rw [← Category.assoc, spMap_evHom hy])
  have huniq : ∀ y (hy : y ∈ P) (f f' : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f →
      F.IsMap (evHom hy) f' → f = f' := fun y hy f f' hf hf' => by
    have e : f.v = f'.v := funext fun τ => funext fun i => (hf τ i).trans (hf' τ i).symm
    cases f; cases f'
    cases e
    rfl

  choose g0 hg0r hg0i hg0 using fun a' b' => x.smoothOn_eigMet σ V φ F τ a' b' hφ
  choose g1 hg1r hg1i hg1 using fun a' b' => hH V φ F τ a' b' hφ
  let M0 := fun y => Matrix.of fun a' b' => g0 a' b' y
  let M1 := fun y => Matrix.of fun a' b' => g1 a' b' y
  have e0 : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMet σ).gram y f τ = M0 y := fun y hy f hf =>
    Matrix.ext fun a' b' => hg0 a' b' y (Set.mem_univ y) hy f hf
  have e1 : ∀ y (hy : y ∈ P), y ∈ Bc → ∀ f, F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ = M1 y :=
    fun y hy hb f hf => Matrix.ext fun a' b' => hg1 a' b' y hb hy f hf
  have p0 : ∀ y ∈ P, (M0 y).PosDef := fun y hy => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e0 y hy f hf ▸ (x.eigMet σ).pos y f τ
  have p1 : ∀ y ∈ P, y ∈ Bc → (M1 y).PosDef := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e1 y hy hb f hf ▸ (x.hodge σ).pos y f τ

  let g : CxPts (genStr s.T.Z) σ → ℂ := fun y =>
    if hy : y ∈ P then (x.eigMetAt σ (some R)).gram y (hfr y hy).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMetAt σ (some R)).gram y f τ a b = g y :=
    fun y hy f hf => by
      simp only [g, dif_pos hy]
      rw [huniq y hy f _ hf (hfr y hy).choose_spec]

  set W := {y : CxPts (genStr s.T.Z) σ | (∏ i, x.nrm σ i y) ^ 2 < Real.exp (Real.exp 1 - R ^ 3)} with hW
  have hcont : ∀ i, Continuous (x.nrm σ i) := fun i => continuous_iff_continuousAt.2 fun y => by
    obtain ⟨V', t, f, hy, -, hf, e⟩ := (x.nrm_div σ i).2 y
    have ho := isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V'.1
    have h1 : ContinuousOn (fun z => √(‖ev (genStr s.T.Z) σ V'.1 t z‖ ^ 2 * Real.exp (-f z))) (ptsIn _ σ V'.1) :=
      (((((manifold s.T.Z σ).holoOn_ev V'.1 t).continuousOn ho).norm.pow 2).mul
        ((hf.continuousOn ho).neg.rexp)).sqrt
    refine (h1.continuousAt (ho.mem_nhds hy)).congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hy) fun z hz => ?_)
    rw [← e z hz, Real.sqrt_sq ((x.nrm_div σ i).1 z).1]
  have hWo : IsOpen W := isOpen_lt ((continuous_finset_prod _ fun i _ => hcont i).pow 2) continuous_const
  have hWbd : ∀ y, LiesIn y (genBd s.T.Z) → y ∈ W := fun y hy => by
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff y).1 hy
    have h0 : x.nrm σ i y = 0 :=
      le_antisymm (not_lt.1 fun h => ((x.nrm_div σ i).pos_iff y).1 h hi) ((x.nrm_div σ i).1 y).1
    show (∏ i, x.nrm σ i y) ^ 2 < _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simpa using Real.exp_pos _
  have hW0 : ∀ y ∈ W, x.wt σ R y = 0 := fun y hy => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact x.wt_eq_zero hR (Or.inl hL)
    · refine x.wt_eq_zero hR (Or.inr ?_)
      have hpos : 0 < (∏ i, x.nrm σ i y) ^ 2 := pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hL i) 2
      have := (Real.log_lt_iff_lt_exp hpos).2 hy
      simp only [OddPrimesWithRootsOfUnity.r]
      linarith

  have hr : (manifold s.T.Z σ).SmoothOn Bc (x.r σ) := by
    refine AnRead.SmoothOn.congr (f := fun y => Real.exp 1 - ∑ i, Real.log (x.nrm σ i y ^ 2))
      (fun c => contDiffOn_const.sub (ContDiffOn.sum fun i _ => ((x.nrm_div σ i).smoothOn_log.mono
        fun y (hy : ¬ LiesIn y (genBd s.T.Z)) hi => hy ((x.liesIn_genBd_iff y).2 ⟨i, hi⟩)) c)) fun y hy => ?_
    simp only [OddPrimesWithRootsOfUnity.r]
    rw [← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero _ (x.nrm_pos hy i).ne']
  have hw : (manifold s.T.Z σ).SmoothOn Bc (x.wt σ R) := by
    refine AnRead.SmoothOn.congr (f := fun y => cutWt x.kap R (x.r σ y)) (fun c => ?_) fun y hy => x.wt_eq hR hy
    have h1 := hr c
    have hpos : ∀ v, 0 < (x.r σ ∘ ((manifold s.T.Z σ).chart c).e.symm) v := fun v =>
      lt_of_lt_of_le (Real.exp_pos 1) (x.exp_le_r σ _)
    have hA := contDiff_cutoff.1.comp_contDiffOn ((h1.log fun v _ => (hpos v).ne').div_const (Real.log R))
    have hB := contDiffOn_const (c := (1 : ℝ)).add ((h1.div_const R).rpow_const_of_ne (p := x.kap)
      fun v _ => (div_pos (hpos v) (by linarith)).ne')
    refine (hA.div hB fun v _ => ?_).congr fun v _ => rfl
    exact (add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (div_nonneg (hpos v).le (by linarith)) _)).ne'

  have hgB : ∀ y ∈ P, y ∈ Bc → g y = (if τ (A.H.rt : D.host.E) = A.H.rt0 then mix (x.wt σ R y) (M0 y) (M1 y)
      else mixDual (x.wt σ R y) (M0 y) (M1 y)) a b := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf]
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [e0 y hy f hf, e1 y hy hb f hf]

  have hgW : ∀ y ∈ P, y ∈ W → g y = g0 a b y := fun y hy hw' => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf, ← hg0 a b y (Set.mem_univ y) hy f hf]
    exact congrFun (congrFun (EigMet.interp_gram_zero (hs := x.wt_mem R) f (hW0 y hw')) a) b

  let T : Bool → Set (CxPts (genStr s.T.Z) σ) := fun β => cond β W Bc
  have key : ∀ β i, ContDiffOn ℝ ∞ (g ∘ ((manifold s.T.Z σ).chart i).e.symm)
      (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) := by
    intro β i
    have sub : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β) ⊆
        ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Set.univ ∩ P) :=
      fun v hv => ⟨hv.1, hv.2.1⟩
    have s0 : EntSm (fun v => M0 (((manifold s.T.Z σ).chart i).e.symm v))
        (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) :=
      fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg0r a' b' i).mono sub, (hg0i a' b' i).mono sub⟩
    cases β
    · have sub1 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Bc ∩ P) :=
        fun v hv => ⟨hv.1, hv.2.2, hv.2.1.2⟩
      have sub2 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' Bc :=
        fun v hv => ⟨hv.1, hv.2.2⟩
      have s1 : EntSm (fun v => M1 (((manifold s.T.Z σ).chart i).e.symm v)) _ :=
        fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg1r a' b' i).mono sub1, (hg1i a' b' i).mono sub1⟩
      have sw := (hw i).mono sub2
      have hf := ite_sm (c := τ (A.H.rt : D.host.E) = A.H.rt0) (mix_sm sw s0 s1)
        (mixDual_sm sw s0 s1 (fun v hv => p0 _ hv.2.1.2) (fun v hv => p1 _ hv.2.1.2 hv.2.2)
          fun v _ => x.wt_mem R _) a b
      refine hf.congr fun v hv => ?_
      simp only [Function.comp]
      rw [hgB _ hv.2.1.2 hv.2.2]
    · refine (s0 a b).congr fun v hv => ?_
      simp only [Function.comp]
      exact hgW _ hv.2.1.2 hv.2.2
  have hT : ∀ β, IsOpen (T β) := fun β => by cases β; exacts [hBo, hWo]
  have hc : ∀ y ∈ Set.univ ∩ P, ∃ β, y ∈ T β := fun y _ => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact ⟨true, hWbd y hL⟩
    · exact ⟨false, hL⟩
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).1,
    AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).2, fun y _ hy f hf => hg y hy f hf⟩

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

theorem exists_fnOf_eq_mul_pow {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint X ∈ U) (p : Γ(X, U)) (hp : fnOf U h p ≠ 0) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen p, RegAt x f) : ∃ (a : Γ(X, U)) (m : ℕ), fnOf U h a = f * fnOf U h (p ^ m) := by
  have hg : genericPoint X ∈ X.basicOpen p := (unitAt_fnOf_iff h h p).1 (unitAt_genericPoint hp)
  obtain ⟨c, rfl⟩ := exists_fnOf_eq hg hf
  have := hU.isLocalization_basicOpen p
  obtain ⟨⟨a, _, m, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) c
  refine ⟨a, m, ?_⟩
  have e' := congrArg (fnOf _ hg) e
  rw [map_mul] at e'
  exact ((fnOf_resG (X.basicOpen_le p) hg a).symm.trans e'.symm).trans
    (congrArg _ (fnOf_resG (X.basicOpen_le p) hg _))

theorem mem_H0_and_vanishOn_of_tendsto : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : GlobalTheory.ProjVar.Var F) (Δ bd : Y.Dv) (g : Y.Fn), Y.Eff bd → (∀ y : Y.X, y ∉ Y.supp bd → Δ.RegularAt y g) → (∀ y ∈ Y.supp bd, ∀ V : Y.X.Opens, y ∈ V → ∃ (U : Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (t : Y.Fnˣ), U ≤ V ∧ (∀ y' ∈ U, Δ.IsEqn y' t) ∧ ∀ (a b : Γ(Y.X, U)) (ψ : ℂ → (Γ(Y.X, U) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec) ≫ Y.str = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∈ Y.supp bd) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∉ Y.supp bd) → fnOf U (gen_mem hy) a = g * t * fnOf U (gen_mem hy) b → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u b ≠ 0) → Tendsto (fun u => ψ u a / ψ u b) (𝓝[≠] 0) (𝓝 0)) → g ∈ Y.H0 Δ ∧ Y.vanishOn Δ g (Y.supp bd) := by
  intro F _ σ Y Δ bd g hbd hreg H
  have key : Y.vanishOn Δ g (Y.supp bd) := by
    intro y hy
    obtain ⟨V, hV, q, hq⟩ := bd.exists_isEqn_nhds y
    obtain ⟨U, hU, hyU, t, hUV, ht, H⟩ := H y hy V hV
    obtain ⟨p, hp⟩ := exists_fnOf_eq (gen_mem hyU)
      fun x hx => CartierDiv.eff_iff.1 hbd x q (hq x (hUV hx))
    have hsupp (x : Y.X) (hx : x ∈ U) : x ∈ Y.supp bd ↔ x ∉ Y.X.basicOpen p := by
      rw [← unitAt_fnOf_iff hx (gen_mem hyU), hp]
      exact (hq x (hUV hx)).mem_supp_iff
    have hp0 : fnOf U (gen_mem hyU) p ≠ 0 := hp ▸ q.ne_zero
    obtain ⟨a, m, ha⟩ := exists_fnOf_eq_mul_pow hU (gen_mem hyU) p hp0 (f := g * t) fun x hx =>
      (ht x (Y.X.basicOpen_le p hx)).regularAt_iff.1
        (hreg x fun h => (hsupp x (Y.X.basicOpen_le p hx)).1 h hx)
    have hφ : Spec.map (Spec.preimage (hU.fromSpec ≫ Y.str)) = hU.fromSpec ≫ Y.str := Spec.map_preimage _
    have := SmoothOfRelativeDimension.smooth Y.dim Y.str
    have hsm : RingHom.Smooth (Spec.preimage (hU.fromSpec ≫ Y.str)).hom :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (by rw [hφ]; infer_instance)
    letI : Algebra F Γ(Y.X, U) := (Spec.preimage (hU.fromSpec ≫ Y.str)).hom.toAlgebra
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    obtain ⟨b, hb, n, hn⟩ := GlobalTheory.T.mem_radical_of_holomorphic_ratio_tendsto F Γ(Y.X, U) hsm σ p a m (fun e => hp0 (by rw [e, map_zero]))
      fun ψ r hψ hσ h0 h1 => H a (p ^ m) ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hsupp _ (spMap_fromSpec_mem hU _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hU _ p s).1 h h0)
        (fun u hu hu0 s h => (hsupp _ (spMap_fromSpec_mem hU _ s)).1 h
          ((spMap_fromSpec_mem_basicOpen hU _ p s).2 (h1 u hu hu0)))
        ha (fun u hu hu0 => by rw [map_pow]; exact pow_ne_zero _ (h1 u hu hu0))
    have e : g * t = fnOf U (gen_mem hyU) b := by
      rw [hb, map_mul] at ha
      exact (mul_right_cancel₀ (by rw [map_pow]; exact pow_ne_zero _ hp0) ha).symm
    refine ⟨t, ht y hyU, e ▸ zeroAt_iff.2 ⟨regAt_fnOf hyU _ b, fun hu => (hsupp y hyU).1 hy ?_⟩⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [unitAt_fnOf_iff hyU, Y.X.mem_basicOpen b y hyU] at hu
    rw [Y.X.mem_basicOpen p y hyU]
    have h := hu.pow n
    rw [← map_pow, ← hc, map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  refine ⟨ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun y => ?_, key⟩
  by_cases hy : y ∈ Y.supp bd
  · exact (key y hy).regularAt
  · exact hreg y hy

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

theorem effCartier_comap_blowup_normal (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0})
    (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') :
    IsProjOver s → Dense ((J.support : Set X)ᶜ) → FinalTheorems.Blowup b J → IsFinite ν →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsIso (ν ∣_ (b ⁻¹ᵁ J.support.compl)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ J.support.compl) : N.Opens) : Set N) →
    ∃ EX : GlobalTheory.EffCartierData N, EX.idealSheaf = J.comap (ν ≫ b) := by
  intro _ _ hbl _ hN _ hd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hbl.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hN y).1) (hd.mono fun z hz => ?_)
    show ν z ∉ D.idealSheaf.support
    rw [hD, Scheme.IdealSheafData.support_comap]
    exact hz
  refine ⟨D.pull ν hK, ?_⟩
  rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoHalfTop

theorem exists_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  intro hC D G _ _ Pl0 T0 A T _ R hvol hJ hcore halg hpb hpre hval hfr hLL hfin hQ hstd hn
  obtain ⟨dict, mu, chiW, x₀, htie, hcore₁⟩ := GlobalTheory.T.exists_core_compatible_adelicData_characters D G Pl0 T0 A T R hvol hJ hcore halg hpre.lev hval hfr
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hpre.lev hpre.fam hpre.models hpre.thP
  obtain ⟨O, hO⟩ := GlobalTheory.T.exists_referenceTuple_thetaComparison_normalisedData D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) hpre hLL htie hpb hQ hstd
  choose cc hcc0 hcc using fun i => GlobalTheory.T.exists_constants_theta_comparison_all_tuples D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O hpre htie
    hpb hfin hQ hio i (hstd i) (hO i)
  obtain ⟨cE, hcE, htie₂, hO₂, hF⟩ := GlobalTheory.T.exists_core_constants_base_solution_equivariant D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O cc
    hpre.lev htie hpb hO hcc0
  obtain ⟨B, hκ, hv, hFB, hpre₂, hchi⟩ := GlobalTheory.T.exists_geometric_half_realisation_geometric_action D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O
    (fun _ => 1) hpre htie₂ hO₂ hF
  obtain ⟨hin, hU, hI⟩ := GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral hC D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) _ (fun _ => 1) B hpre₂ hchi hpb hn
  refine ⟨dict, mu, chiW, x₀, cE, _, _, B, hκ, hin, hFB, fun i => ⟨⟨_, _, hFB.1 i⟩, fun _ => ?_⟩,
    GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ _ hpre₂.lev hpre₂.fam hpre₂.models hpre₂.thP, hpre₂, hchi, hU, hI, hcore₁⟩
  obtain ⟨O', h1, h2, h3⟩ := hcc i
  obtain ⟨O'', e1, -, p1, p2⟩ := GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R)
    (nTop (reCore T dict mu chiW x₀ cE) (kapTop D)) (formsGeo (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O) i T0 id O'
  rw [hκ, hv]
  refine ⟨O'', ?_, p1 h2, ?_⟩
  · rw [e1]; exact h1
  · rw [← hcE i] at h3
    exact p2 _ _ h3

end GlobalTheory.GeoHalfTop

end
end

