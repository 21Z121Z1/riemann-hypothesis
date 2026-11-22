import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0048
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiscrPowerBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerBasisDiscr

private theorem val_discr {C : Type} [Field C] (v : Valuation C NNReal) {n : ℕ} (a : Fin n → C) :
    v (discr a) = v ((Matrix.vandermonde a).det ^ 2) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j : Fin n => v (a j - a i))
  rw [Matrix.det_vandermonde, map_pow, Up.discr]
  simp only [map_prod]
  rw [sq, ← Finset.prod_mul_distrib]
  simp only [← Finset.prod_mul_distrib]
  have h2 : ∀ i : Fin n, Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    intro i; ext j; simp
  simp only [h2]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Valuation.map_sub_swap v (a i) (a j)]

private theorem inj_of_discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : discr a ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (i := j) ?_ ?_)
  · simp [Ne.symm hne]
  · rw [hij, sub_self]

private theorem det_change {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] {n : ℕ} (b b' : Module.Basis (Fin n) R M) (f : Fin n → M →ₗ[R] O) :
    ∃ u : O, IsUnit u ∧ (Matrix.of fun i j => f j (b' i)).det = u * (Matrix.of fun i j => f j (b i)).det := by
  refine ⟨algebraMap R O (b.toMatrix b').det, ?_, ?_⟩
  · exact (b.isUnit_det b').map _
  · rw [← Matrix.det_transpose (b.toMatrix b'), RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr (b' i)]
    simp only [map_sum, map_smul, Algebra.smul_def]

theorem discr_power_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → Function.Injective (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) ∧ 0 ≤ (w.n : ℝ) * vd ∧ (v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) : ℝ) = (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd) := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ w t vd hvd α b hb
  obtain ⟨b', hb'⟩ := hvd
  obtain ⟨u, hu, hdet⟩ := det_change b b'
    (fun j => (tauExt ((t j : Emb (O := O) w.e) : OE →+* O)).toLinearMap ∘ₗ w.Ow.subtype)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply] at hdet
  have hM : (Matrix.of fun i j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) =
      (Matrix.vandermonde fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)ᵀ := by
    ext i j
    have h1 : tauExt ((t j : Emb (O := O) w.e) : OE →+* O) w.e = 1 := (t j).2
    simp [hb, h1, Matrix.vandermonde_apply]
  have hvu : v (algebraMap O C u) = 1 := hv.isUnit_iff_valuation_eq_one.1 hu
  have key : v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) =
      v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) := by
    rw [val_discr, hdet, hM, Matrix.det_transpose, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
      hvu, one_pow, _root_.one_mul, map_pow, map_pow, RingHom.map_det]
    congr 3
    ext i j
    simp [Matrix.vandermonde_apply]
  have hq0 : 0 < (v (algebraMap O C (p : O)) : ℝ) := by
    have : v (algebraMap O C (p : O)) ≠ 0 := by
      rw [map_natCast, Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hq1 : (v (algebraMap O C (p : O)) : ℝ) < 1 := by
    have : v (algebraMap O C (p : O)) < 1 :=
      lt_of_le_of_ne (hv.map_le_one _) fun h => hp.out (hv.isUnit_iff_valuation_eq_one.2 h)
    exact_mod_cast this
  refine ⟨?_, ?_, by rw [key, hb']⟩
  · refine Function.Injective.of_comp (f := algebraMap O C) (inj_of_discr _ fun h0 => ?_)
    have h3 := Real.rpow_pos_of_pos hq0 ((w.n : ℝ) * vd)
    rw [← hb', ← key] at h3
    have h4 : discr (fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) = 0 := h0
    rw [h4] at h3
    simp at h3
  · by_contra hneg
    have h3 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hq0 hq1 (not_le.1 hneg)
    rw [← hb'] at h3
    have h4 := hv.map_le_one (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)
    exact absurd h4 (not_le.2 (by exact_mod_cast h3))

end GlobalTheory.PowerBasisDiscr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ChF

private theorem exists_leftInv {O OE : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing OE] {d n : ℕ}
    (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O) (h : EigB ρ τ W) :
    ∃ G : Matrix (Fin n) (Fin d) O, ∀ i, G *ᵥ W i = Pi.single i 1 := by
  classical
  let φ : (Fin n → O) →ₗ[O] (Fin d → O) := Fintype.linearCombination O W
  have hφ : ∀ c, φ c = ∑ i, c i • W i := fun c => Fintype.linearCombination_apply O W c
  have heig : ∀ c a, (ρ a) *ᵥ φ c = τ a • φ c := by
    intro c a
    rw [hφ, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, h.1, smul_comm]
  have hinj : Function.Injective φ := by
    intro c c' hc
    obtain ⟨c₀, -, hu⟩ := h.2 (φ c) (heig c)
    rw [hu c (hφ c).symm, hu c' (by rw [hc]; exact (hφ c').symm)]
  have htf : Submodule.torsion O ((Fin d → O) ⧸ LinearMap.range φ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht⟩, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hx' : (Submodule.Quotient.mk (t • y) : (Fin d → O) ⧸ LinearMap.range φ) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hy : ∀ a, (ρ a) *ᵥ y = τ a • y := by
      intro a
      have := heig c a
      rw [hc, Matrix.mulVec_smul, smul_comm] at this
      exact smul_right_injective _ ht0 this
    obtain ⟨c₀, hc₀, -⟩ := h.2 y hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨c₀, (hφ c₀).trans hc₀⟩
  haveI : Module.Flat O ((Fin d → O) ⧸ LinearMap.range φ) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htf
  haveI : Module.Free O ((Fin d → O) ⧸ LinearMap.range φ) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y, (LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ : (Fin d → O) →ₗ[O] (Fin d → O)) y ∈ LinearMap.range φ := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]
  let g : (Fin d → O) →ₗ[O] (Fin n → O) :=
    (LinearEquiv.ofInjective φ hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hg : ∀ c, g (φ c) = c := by
    intro c
    have h0 : (LinearMap.range φ).mkQ (φ c) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨c, rfl⟩
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    ext1
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h0,
      map_zero, sub_zero, LinearEquiv.ofInjective_apply]
  refine ⟨LinearMap.toMatrix' g, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, ← hg (Pi.single i 1), hφ]
  congr 1
  simp [Pi.single_apply]

theorem eigB_res_surjective : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  classical
  intro C _ v O _ _ hv OE _ d n ρ τ W h
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨G, hG⟩ := exists_leftInv ρ τ W h
  refine ⟨fun c => ⟨Gᵀ *ᵥ c, ?_⟩, fun a f => ?_, ?_⟩
  · have h1 : Matrix.of W * Gᵀ = 1 := by
      ext i k
      have := congrFun (hG i) k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm (a := i), ← this, mul_comm]
    simp only [Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · ext i
    have : Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) i = W i ⬝ᵥ ((ρ a)ᵀ *ᵥ f) := rfl
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1, smul_dotProduct]
    rfl
  · let W' : Fin n → Fin d → C := fun i => algebraMap O C ∘ W i
    have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin d) O) (y : Fin d → O),
        M.map (algebraMap O C) *ᵥ (algebraMap O C ∘ y) = algebraMap O C ∘ (M *ᵥ y) := by
      intro m M y
      ext k
      exact (RingHom.map_mulVec (algebraMap O C) M y k).symm
    have hli : LinearIndependent C W' := by
      refine LinearIndependent.of_comp (Matrix.mulVecLin (G.map (algebraMap O C))) ?_
      have : (Matrix.mulVecLin (G.map (algebraMap O C))) ∘ W' = Pi.basisFun C (Fin n) := by
        funext i
        simp only [Function.comp_apply, Matrix.mulVecLin_apply, W', hmap, hG]
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact (Pi.basisFun C (Fin n)).linearIndependent
    have hsp : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (((algebraMap O C).comp τ) a)) = Submodule.span C (Set.range W') := by
      apply le_antisymm
      · intro x hx
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
        obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
        choose y hy using hbx
        have hb0 : algebraMap O C b ≠ 0 := by
          rw [map_ne_zero_iff _ hv.hom_inj]; exact nonZeroDivisors.ne_zero hb
        have hyx : algebraMap O C ∘ y = algebraMap O C b • x := by
          ext k
          simp only [Function.comp_apply, hy k, Pi.smul_apply, Algebra.smul_def]
          rfl
        have hye : ∀ a, (ρ a) *ᵥ y = τ a • y := by
          intro a
          ext k
          apply hv.hom_inj
          have := congrFun (hmap (ρ a) y) k
          rw [hyx, Matrix.mulVec_smul, hx a, smul_comm, ← hyx] at this
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.comp_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← this]
        obtain ⟨c, hc, -⟩ := h.2 y hye
        rw [← Submodule.smul_mem_iff _ hb0, ← hyx, ← hc]
        have : algebraMap O C ∘ (∑ i, c i • W i) = ∑ i, algebraMap O C (c i) • W' i := by
          ext k
          simp [W', Finset.sum_apply, Algebra.smul_def]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        intro a
        simp only [W', hmap, h.1]
        ext k
        simp
    unfold eigDim
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimitStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit

namespace GlobalTheory.ActionEnd

variable {C : Type} [Field C]

theorem germ_comp1_zero_point_left {dd n : ℕ} (a : Pt C n dd) (ha : GP a) : comp1 (pt C dd (0 : Fin 1)) a = a := by
  funext i
  rw [germComp1_eq_subst]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) _

theorem actK_self [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (B : FB C dd O) (a : O) :
    B.actK C a = B.A.act a := by
  funext i
  show MvPowerSeries.map (RingHom.id C) _ = _
  rw [MvPowerSeries.map_id]; rfl

theorem exists_isEnd_act : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  intro C _ _ V O _ _ dd Y d _ I _ p a
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine ⟨dLin (Y.B.A.act a), dLin (Y.B.A.act (star a)), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · refine isEnd_of_hom Y p _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
    have h := Y.gauge.ad a
    rw [actK_self, actK_self] at h
    rw [← h]
    have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
      show MvPowerSeries.map (RingHom.id C) _ = _
      rw [MvPowerSeries.map_id]; rfl
    rw [e]
    exact Y.intAd a
  · have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
    have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
    have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
    have hs : MvPowerSeries.HasSubst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
    have e1 := matrixEnd_eq_subst Y p (pt C dd 0) q0 (by
      rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
    rw [germLinearPart_coordinatePoint_zero] at e1
    have e2 := matrixEnd_eq_subst Y p _ (g a) (Y.B.A.hom a) _ hX
    have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
      funext i
      rw [germComp1_eq_subst]
      have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
        funext ⟨s, x⟩
        obtain rfl : s = 0 := Subsingleton.elim _ _
        rfl
      rw [this, MvPowerSeries.subst_self]; rfl
    have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
      rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
    rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
      hEnd, hAt]
    show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
    congr 1
    funext ⟨s, x⟩
    fin_cases s
    · exact (e1 x).symm
    · exact (e2 x).symm

end GlobalTheory.ActionEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimit
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex in
theorem matrixEnd_linearMap' (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP X M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := by
    unfold endP
    rw [hlg, hex]
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

include hlg hex in
theorem matrixEnd_eq_subst' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap' Y X hlg hex _ a ha, ← eq_exp_lin_log Y e he hhom]

include hlg hex in
theorem matrixEnd_eq_comp' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP X (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst' Y X hlg hex e he hhom a ha, germComp1_eq_subst]

include hh in
theorem hAt_eq_ev_raw {n : ℕ} (a b : Pt C n dd) : hAt X a b = ev ![a, b] Y.h := by
  unfold hAt
  rw [hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

include hlg hex hh in
theorem isEnd_of_hom_raw (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd X V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst' Y X hlg hex e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst' Y X hlg hex e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp' Y X hlg hex e he hhom _ (gp_pt 0), matrixEnd_eq_comp' Y X hlg hex e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev_raw Y X hh, hAt_eq_ev_raw Y X hh, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit_raw : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d I X hlg hex hh a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom_raw Y X hlg hex hh fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom_raw Y X hlg hex hh f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLadicSeparatingSequenceEmbeddingsStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ladic_separating_sequence_embeddings : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (1 - em a (s n))) ∧ ∀ φ : O →+* C, (∀ x, V.Ge 0 (φ x)) → (∀ a, ∃ x, V.v (em a x - φ x) = 0) → ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (0 - φ (s n)) := by
  first | exact @GlobalTheory.SeparatingSeq.main | exact GlobalTheory.SeparatingSeq.main | (intros; apply GlobalTheory.SeparatingSeq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement
section
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialBlock_supply_both_typings : MONSupply ∧ RF.MONSupply := by
  first | exact @GlobalTheory.MonBlock.monSupply | exact GlobalTheory.MonBlock.monSupply | (intros; apply GlobalTheory.MonBlock.monSupply <;> assumption)
end

