import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frPt_tie : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R, (∀ τ i, M.Eig f τ (fun j => u τ j i)) → (∀ τ cv, M.Eig f τ cv → ∃! a : Fin (Dw.mult τ) → R, (u τ).mulVec a = cv) → ∃ y : FrPt Xo c R, y.x = x ∧ M.Comparison₂ f u y := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ u hu huniq
  have hover : x ≫ Xo.s = sOf c R := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    unfold sOf spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hV := GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M R f x Λ
  choose w hw _ using fun τ (i : Fin (Dw.mult τ)) => hV.1 (fun j => u τ j i)
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.exists_chart_generator_pullback_generates_fibre hT E H Dw l Xo c O β Y M R f x Λ
  refine ⟨⟨x, hover, w, fun τ i => hV.2.1 _ _ (hw τ i),
    fun τ i => (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ _ _ (hw τ i)).2 (hu τ i), ?_, s, hgen⟩,
    rfl, Λ, fun τ i => hw τ i, hs⟩
  intro τ v hvt hve
  obtain ⟨cv, hcv, hcvu⟩ := hV.2.2 v hvt
  have hcomb : ∀ a, IsCombAt x (w τ) a v ↔ Λ.Vec ((u τ).mulVec a) v := by
    intro a
    have hsum : (∑ i, a i • fun j => u τ j i) = (u τ).mulVec a := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M R f x Λ _ (fun i j => u τ j i) (w τ) a v (hw τ), hsum]
  have hcve : M.Eig f τ cv := (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ cv v hcv).1 hve
  obtain ⟨a, ha, hau⟩ := huniq τ cv hcve
  refine ⟨a, (hcomb a).2 (ha ▸ hcv), fun a' ha' => hau a' ?_⟩
  exact hcvu _ ((hcomb a').1 ha')

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointIntegralIntegralCellAnyModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_integral_integralCell_anyModel : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  first | exact @GlobalTheory.Reg.tie_integral_of_any_model | exact GlobalTheory.Reg.tie_integral_of_any_model | (intros; apply GlobalTheory.Reg.tie_integral_of_any_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularInvOfDiagNe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem triangular_inv_of_diag_ne {L : Type} [Field L] {n : ℕ} (b : Matrix (Fin n) (Fin n) L)
    (hb : b.BlockTriangular id) (hd : ∀ i, b i i ≠ 0) :
    b * b⁻¹ = 1 ∧ (b⁻¹).BlockTriangular id ∧ ∀ i, b⁻¹ i i ≠ 0 := by

  have hdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  let _ : Invertible b := Matrix.invertibleOfIsUnitDet b hdet
  have htri : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.mul_nonsing_inv b hdet, htri, fun i => ?_⟩

  have hii : (b⁻¹ * b) i i = b⁻¹ i i * b i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hki with h | h
    · rw [htri h, zero_mul]
    · rw [hb h, mul_zero]
  rw [Matrix.nonsing_inv_mul b hdet, Matrix.one_apply_eq] at hii
  exact left_ne_zero_of_mul_eq_one hii.symm

theorem scal_mul_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a a' : S) (i : (PPx x).ι) :
    scal x (a * a') i = scal x a i * scal x a' i := by
  simp only [scal, map_mul, Out.liftFun]

theorem scal_one_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  simp only [scal, map_one, Out.liftFun]

theorem frBor_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y z : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), z.x = y.x → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → M.Comparison₂ f u z → ∃ t : Ix Dw → Lˣ, FrBor t y z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f y z Λ u b hxz hb hΛ hM
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  subst hxz
  obtain ⟨Λ', hΛ'u, -⟩ := hM

  have hB : ∀ τ, b τ * (b τ)⁻¹ = 1 ∧ ((b τ)⁻¹).BlockTriangular id ∧ ∀ i, (b τ)⁻¹ i i ≠ 0 :=
    fun τ => triangular_inv_of_diag_ne (b τ) (hb τ).1 (hb τ).2

  obtain ⟨a, ha, -⟩ := y.gen zs
  obtain ⟨a', ha', -⟩ := zg y.s
  obtain ⟨w, -, huniq⟩ := zg zs
  have h1 : ∀ i, zs.f i = scal y.x (a * a') i * zs.f i := fun i => by
    rw [scal_mul_tie, _root_.mul_assoc, ← ha' i, ← ha i]
  have h2 : ∀ i, zs.f i = scal y.x 1 i * zs.f i := fun i => by
    rw [scal_one_tie, _root_.one_mul]
  have haa : a * a' = 1 := (huniq _ h1).trans (huniq _ h2).symm
  refine ⟨fun k => Option.elim k (Units.mkOfMulEqOne a a' haa)
    (fun p => Units.mk0 ((b p.1)⁻¹ p.2 p.2) ((hB p.1).2.2 p.2)), ?_⟩
  unfold FrBor
  refine ⟨rfl, fun τ i => ⟨fun j => (b τ)⁻¹ j i, rfl, fun j hij => (hB τ).2.1 hij, ?_⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  ·
    refine (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M L f y.x Λ (Dw.mult τ) (fun j k => (u τ * b τ) k j)
      (y.u τ) (fun j => (b τ)⁻¹ j i) (zu τ i) (fun j => hΛ τ j)).mpr ?_
    have hv := (GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f y.x Λ' Λ).1 _ _ (hΛ'u τ i)
    convert hv using 1
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (b τ)⁻¹ j i * (u τ * b τ) k j = (u τ * b τ * (b τ)⁻¹) k i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
      _ = u τ k i := by rw [Matrix.mul_assoc, (hB τ).1, Matrix.mul_one]
  ·
    have e : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, e, Option.elim_none, Units.val_mkOfMulEqOne]
    erw [op_id, CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.hom_id, RingHom.id_apply]
    exact (ha i).symm

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.values_eq_of_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  first | exact @GlobalTheory.Reg.FChart.compat | exact GlobalTheory.Reg.FChart.compat | (intros; apply GlobalTheory.Reg.FChart.compat <;> assumption)
end

