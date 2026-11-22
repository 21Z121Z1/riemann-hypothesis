import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0788
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0793

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram GlobalTheory.TrueCx Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeGenUnf

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_mem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : Formalism.L2.PjFree.relab c σ τ.1 ∈ (U.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ.1).2 τ.2)

theorem comb_unitary {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x x₁ : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k) x₁.1)
    (e : (U.un k x₁).x = (U.un k x).x) (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hT : ∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) ((U.un k x₁).u τ b)) :
    Tᴴ * T = 1 :=
  GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary hσ hU k x x₁ hx hx₁ e τ T hT

theorem uniformisation_component_eq_of_same_modulusPoint {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨g0, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem unitary_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)} (hf : IsHodgeFrame Uf y f) (hg : IsHodgeFrame Uf y g)
    (τ : E →+* ℂ) : (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  have e1 : σ = σ' := by_contra fun h => (hE σ' (Ne.symm h)).false k
  have e2 : σ = σ₁ := by_contra fun h => (hE σ₁ (Ne.symm h)).false k₁
  subst e1 e2
  have hid : ∀ {ψ : ℂ →+* ℂ}, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) → σ = ψ.comp σ → ψ = RingHom.id ℂ := by
    intro ψ h h'
    rcases h with rfl | rfl
    · rfl
    · exact (not_good_conj c (σ := σ) hσ (h' ▸ hσ)).elim
  obtain rfl := hid h1 h2
  obtain rfl := hid g1 g2
  have hx : (cxPt Z ((Uf σ).un k x)).1 ≫ genι Z = spMap (RingHom.id ℂ) ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap (RingHom.id ℂ) h2 hx
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  obtain rfl : k = k₁ := (uniformisation_component_eq_of_same_modulusPoint hσ hU x x₁ e.symm).symm
  have key := comb_unitary hσ hU k x x₁ h4 g4 e τ _ (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  rw [h6.co τ hg' hx] at key
  convert key using 2 <;> ext <;> simp

theorem gram_eq_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ} {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : IsHodgeFrame Uf y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge Uf b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame Uf y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    unitary_of_single hE hσ hU h.choose_spec hf, Matrix.one_mul]

theorem unfFam_empty (U : Formalism.L2.PjFree.Unf Xo c σ r) (σ' : c.F →+* ℂ) (h : σ' ≠ σ) :
    IsEmpty (unfFam U σ').Comp := by
  unfold unfFam
  rw [dif_neg (Ne.symm h)]
  exact inferInstanceAs (IsEmpty Empty)

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := dif_pos rfl

theorem isHodgeFrame_of_eq {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hq : Uf σ = U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) :
    IsHodgeFrame (Z := Z) Uf (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) := by
  subst hq
  exact isHodgeFrame_cxFrame hσ hx

variable (Z) in

theorem hodgeMet_gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  rw [hodgeMet, gram_eq_of_single (unfFam_empty U) hσ ((unfFam_self U).symm ▸ hU)
    (isHodgeFrame_of_eq (unfFam_self U) hσ hx), EigFrame.co_self, conjTranspose_one, Matrix.mul_one]

end GlobalTheory.HodgeGenUnf

namespace GlobalTheory.HodgeGenUnf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

def letter {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : (U.X k).Ψ :=
  ⟨Formalism.L2.PjFree.relab c σ τ.1, relab_mem hσ hU k τ⟩

theorem mult_psi (τ : GlobalTheory.AllWt.Psi H) : Dw.mult τ.1 = Dw.p := if_pos τ.2

variable (Z) in

theorem hodgeMet_gram_frame {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (f : (U.X k).dom) (τ : GlobalTheory.AllWt.Psi H) (τ' : (U.X k).Ψ)
    (hτ : τ'.1 = Formalism.L2.PjFree.relab c σ τ.1) (hj : Dw.p ≤ Dw.p + Dw.q) :
    ((hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1).submatrix
        (Fin.cast (mult_psi τ).symm) (Fin.cast (mult_psi τ).symm) =
      ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) hj f.1 τ')ᴴ * (hP (moeb (frameCo (U.X k) hj f.1 τ') 0))⁻¹ *
        coW (U.X k) hj f.1 τ') := by
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k) f.1 f.2
  let f' : (U.X k).dom := ⟨x1, KU.orth_dom _ h1⟩
  have hz : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f.1 = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f'.1 := by
    show domPt _ _ _ f.1 = domPt _ _ _ x1
    rw [ef, domPt_rmul _ _ _ hb]
  have hmo : ∀ ρ : (U.X k).Ψ, moeb (frameCo (U.X k) hj f.1 ρ) 0 = moeb (frameCo (U.X k) hj f'.1 ρ) 0 :=
    fun ρ => congrFun hz ρ
  have h1' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f.2 f'.2 ρ (hmo ρ)
  have h2' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f'.2 f.2 ρ (hmo ρ).symm
  have hx : (U.un k f).x = (U.un k f').x := PointWell.pt_eq_of_block hU hσ k f f' h1' h2'
  have hg : (hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1 =
      (Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i)ᴴ *
        (hodgeMet Z U).gram (cxPt Z (U.un k f')) (cxFrame Z (U.un k f')) τ.1 *
        Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i :=
    eigGram_of_comb (hodgeMet Z U) _ _ hx τ.1 _ (fun i => lie_comb_of_block hU hσ k f f' h1' h2' τ.1 i)
  rw [hg, hodgeMet_gram_orth Z hσ hU (x := f') h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_submatrix_sq]
  set e := Fin.cast (mult_psi τ).symm
  have he : Function.Bijective e := (finCongr (mult_psi τ).symm).bijective
  rw [Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
  have hKe : (Matrix.of fun b i : Fin (Dw.mult τ.1) =>
      coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i).submatrix e e =
      Matrix.of fun b i : Fin Dw.p => coef (U.X k) f.1 f'.1 τ'.1 b i := by
    ext b i; rw [hτ]; rfl
  obtain ⟨hco1, -⟩ := hodge_co (U.X k) hj hp h1 τ'
  rw [hKe, coef_eq_coW_change (U.X k) hj hp f.2 f'.2 τ' (hmo τ'), hmo τ',
    eq_of_conj_eq_one (isUnit_coW _ _ hp f'.2 _) hco1]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeGenUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNull
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifNull

open Set in

theorem iSup_apply_eq_zero {Z : Type*} [MeasurableSpace Z] {ι : Type*} (μ : ι → Measure Z) {T : Set Z}
    (hT : MeasurableSet T) (h : ∀ i, μ i T = 0) : (⨆ i, μ i) T = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Tᶜ := iSup_le fun i => Measure.le_iff.2 fun B hB => by
    rw [Measure.restrict_apply hB, ← measure_inter_add_diff B hT, diff_eq,
      measure_mono_null inter_subset_right (h i), zero_add]
    exact Measure.le_iff'.1 (le_iSup μ i) _
  refine le_antisymm ((Measure.le_iff'.1 hle T).trans ?_) (zero_le)
  rw [Measure.restrict_apply hT, inter_compl_self, measure_empty]

open Set in

theorem glueNull : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : AlgChart p σ D → CxPts p σ → ENNReal) (S : Set (CxPts p σ)), (∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ S)) = 0) → glueMeas (fun c : AlgChart p σ D => c.e) ρ S = 0 := by
  intro k _ Y p σ D _ ρ S hS
  classical
  obtain ⟨I, hIc, hI⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
  let Z : AlgChart p σ D → Set (ReciprocityTheory.L2DbarEstimates.V D) := fun c => toMeasurable volume (c.e '' (c.e.source ∩ S))
  have hZ : ∀ c, volume (Z c) = 0 := fun c => (measure_toMeasurable _).trans (hS c)
  have hTm : ∀ c : AlgChart p σ D, MeasurableSet (c.e.source ∩ c.e ⁻¹' Z c) := by
    intro c
    have hm := (c.e.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ReciprocityTheory.L2DbarEstimates.V D)))
      c.e.open_source.measurableSet) (measurableSet_toMeasurable volume (c.e '' (c.e.source ∩ S)))
    convert c.e.open_source.measurableSet.inter hm using 1
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> simpa [Set.piecewise_eq_of_mem _ _ _ h1] using h2
  let T : Set (CxPts p σ) := (⋃ c : AlgChart p σ D, c.e.source)ᶜ ∪ ⋃ c ∈ I, (c.e.source ∩ c.e ⁻¹' Z c)
  have hT : MeasurableSet T :=
    (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet.compl.union
      (MeasurableSet.biUnion hIc fun c _ => hTm c)
  have hST : S ⊆ T := by
    intro y hy
    by_cases hO : y ∈ ⋃ c : AlgChart p σ D, c.e.source
    · right
      rw [← hI] at hO
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hO
      exact mem_biUnion hc ⟨hyc, subset_toMeasurable _ _ ⟨y, ⟨hyc, hy⟩, rfl⟩⟩
    · exact Or.inl hO
  have hc0 : ∀ c : AlgChart p σ D, chartMeas c.e (ρ c) T = 0 := by
    intro c
    rw [chartMeas_apply _ _ hT]
    refine setLIntegral_measure_zero _ _ ?_
    have hsub : c.e '' (c.e.source ∩ T) ⊆ ⋃ c' ∈ I, (c.e ∘ c'.e.symm) ''
        (Z c' ∩ (c'.e.target ∩ c'.e.symm ⁻¹' c.e.source)) := by
      rintro _ ⟨y, ⟨hy, hyT⟩, rfl⟩
      rcases hyT with hyO | hyT
      · exact (hyO (mem_iUnion.2 ⟨c, hy⟩)).elim
      obtain ⟨c', hc', hy1, hy2⟩ := mem_iUnion₂.1 hyT
      refine mem_biUnion hc' ⟨c'.e y, ⟨hy2, c'.e.map_source hy1, ?_⟩, ?_⟩
      · simp only [mem_preimage, c'.e.left_inv hy1]; exact hy
      · simp only [Function.comp_apply, c'.e.left_inv hy1]
    refine measure_mono_null hsub ((measure_biUnion_null_iff hIc).2 fun c' _ => ?_)
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (((AlgChart.holo_trans c' c).restrictScalars ℝ).mono inter_subset_right)
      (measure_mono_null inter_subset_left (hZ c'))
  exact measure_mono_null hST (iSup_apply_eq_zero _ hT hc0)

open Set in

theorem volume_null_of_muD {ι : Type} [Fintype ι] {p q : ℕ} {N : Set (ι × Fin p × Fin q → ℂ)}
    (hN : N ⊆ DomFlat ι p q) (h0 : muD ι p q N = 0) : volume N = 0 := by
  have hc : ∀ i : ι, Continuous fun v : ι × Fin p × Fin q → ℂ => (hQ (unflat v i)).det.re := by
    intro i
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    have hu : Continuous fun v : ι × Fin p × Fin q → ℂ => unflat v i :=
      continuous_pi fun a => continuous_pi fun b => continuous_apply (i, a, b)
    unfold hQ
    exact continuous_const.sub (Continuous.matrix_mul (Continuous.matrix_conjTranspose hu) hu)
  have hm : Measurable fun v : ι × Fin p × Fin q → ℂ =>
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
    simp only [zpow_neg, zpow_natCast]
    exact ((hc i).measurable.pow_const _).inv
  have hpos : ∀ v ∈ DomFlat ι p q,
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) ≠ 0 := by
    intro v hv
    refine (ENNReal.ofReal_pos.2 (Finset.prod_pos fun i _ => zpow_pos ?_ _)).ne'
    have h := (hv i : (1 - (unflat v i)ᴴ * unflat v i).PosDef).det_pos
    exact (Complex.pos_iff.1 h).1
  rw [muD, withDensity_apply_eq_zero' hm.aemeasurable,
    Measure.restrict_apply' GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.measurableSet] at h0
  refine measure_mono_null ?_ h0
  intro v hv
  exact ⟨⟨hpos v (hN hv), hv⟩, hN hv⟩

open Set in

theorem chart_image_null {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ι : Type} [Fintype ι] (c : AlgChart p σ D) (ψ : (ι → ℂ) → CxPts p σ) {s : Set (ι → ℂ)}
    (hD : D = Fintype.card ι) (hs : volume s = 0)
    (hψ : ∀ a, DifferentiableOn ℂ (ev p σ c.U (c.x a) ∘ ψ) (s ∩ ψ ⁻¹' ptsIn p σ c.U)) :
    volume (c.e '' (c.e.source ∩ ψ '' s)) = 0 := by
  set t := s ∩ ψ ⁻¹' c.e.source with ht
  have e1 : c.e '' (c.e.source ∩ ψ '' s) = (c.e ∘ ψ) '' t := by
    ext y; constructor
    · rintro ⟨_, ⟨h1, w, hw, rfl⟩, rfl⟩; exact ⟨w, ⟨hw, h1⟩, rfl⟩
    · rintro ⟨w, ⟨hw, h1⟩, rfl⟩; exact ⟨ψ w, ⟨h1, w, hw, rfl⟩, rfl⟩
  have hd : DifferentiableOn ℂ (c.e ∘ ψ) t :=
    differentiableOn_euclidean.2 fun a => ((hψ a).mono fun w hw => ⟨hw.1, c.source_subset hw.2⟩).congr
      fun w hw => c.apply_eq _ hw.2 a
  have hfin : Module.finrank ℝ (ι → ℂ) = Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V D) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ι → ℂ), ← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V D)]
    simp [hD]
  let L : (ι → ℂ) ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V D := ContinuousLinearEquiv.ofFinrankEq hfin
  have h1 : volume ((L.symm ∘ (c.e ∘ ψ)) '' t) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (L.symm.differentiable.comp_differentiableOn (hd.restrictScalars ℝ))
      (measure_mono_null inter_subset_left hs)
  have e2 : (c.e ∘ ψ) '' t = L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t) := by
    rw [← L.image_eq_preimage_symm, image_image]; simp
  haveI : (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))).IsAddHaarMeasure :=
    L.symm.isAddHaarMeasure_map volume
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure
    (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))) volume
  rw [e1, e2]
  calc volume (L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t))
      = Measure.map L.symm volume ((L.symm ∘ (c.e ∘ ψ)) '' t) :=
        (L.symm.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = 0 := hac h1

theorem image_null : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ N ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) N = 0 → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' N) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ N hN h0
  have hH := GlobalTheory.T.uniformisationComponent_holomorphic_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hv := volume_null_of_muD hN h0
  have hdim : X.dim = Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) := by
    rw [(GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL).2]
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.two_card_Psi (U.X k)
    have h2 : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
      rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
    have h3 : Fintype.card (GlobalTheory.AllWt.Psi H) = Fintype.card (U.X k).Ψ := by omega
    simp only [Fintype.card_prod, Fintype.card_fin, h3, Nat.add_sub_cancel_left]
  unfold chernTopPart
  exact glueNull X.str (σ.comp e.toRingHom) X.dim _ _ fun ch =>
    chart_image_null ch ψ hdim hv fun a => (hH ch.U (ch.x a)).mono fun w hw => ⟨hN hw.1, hw.2⟩

end GlobalTheory.UnifNull
end

