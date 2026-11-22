import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLaw
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem cartHyp_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → (∀ g, HasTeich X V g) → ∀ g, X.CartHyp V g := by
  intro C _ V d _ I _ κ _ X hL hP hT g
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hL.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hh := hL.axes 0
  refine
    { zero := X.zero_mem hlg0 hh V g
      add := X.add_mem V g (GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hL) hL.uint
      neg := X.neg_mem V g hL.odd
      teich := X.teich_mem V g
      Vm := X.V_mem V g
      Fm := GlobalTheory.T.frobenius_mem_typicalCurveSet C V d I κ X hL g
      sumV := GlobalTheory.T.shiftedSum_mem_typicalCurveSet C V d I κ X hL g
      t2 := X.val_nonneg_leading_coeff_of_mem_tySet V g hL.lin hh ?_ (GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne C V d I κ X hL g (hT g))
      t3 := X.const_mem_type_set_of_nonneg hlg0 hh V g
      t4 := GlobalTheory.T.exists_pure_typical_curve_with_integral_tangent C V d I κ X hL hP g (hT g) }
  obtain ⟨w, hw, huw⟩ := hL.sat g
  refine ⟨w, hw, fun c c' => ?_⟩
  split_ifs with h
  · exact (huw c c').1 h
  · exact (huw c c').2 h

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceLinearData
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem lav_fp {O : Type} [CommRing O] {J : Type} [Fintype J]
    (h : ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M →
      Module.FinitePresentation O (M ⧸ N.comap M.subtype))
    (M N : Submodule O (J → O)) (hM : M.FG) (hN : N.FG) (hle : N ≤ M) :
    Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  let e : (J → O) ≃ₗ[O] (Fin (Fintype.card J) → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin J).symm
  have h1 := h _ (M.map e.toLinearMap) (N.map e.toLinearMap) (hM.map _) (hN.map _)
    (Submodule.map_mono hle)
  refine Module.FinitePresentation.of_equiv
    (Submodule.Quotient.equiv ((N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype) (N.comap M.subtype)
      (e.submoduleMap M).symm ?_)
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have : (((e.submoduleMap M).symm y : M) : J → O) = z := by
      rw [LinearEquiv.submoduleMap_symm_apply, ← hzy]
      exact e.symm_apply_apply z
    exact this ▸ hz
  · intro hx
    exact ⟨e.submoduleMap M x, ⟨x, hx, rfl⟩, (e.submoduleMap M).symm_apply_apply x⟩

private theorem lav_num (P D c cw X : ℝ) (n rm vd q : ℝ) (rp rm' h : ℕ) (hrm : rm = rm')
    (hP0 : 0 < P) (hP1 : P ≤ 1) (hvd : 0 ≤ n * vd) (hD : D = P ^ (n * vd)) (hh : h ≤ rp + rm')
    (hcw : P ^ ((n * rm) / q) ≤ cw) (hc : cw ≤ c) (hX : 0 ≤ X)
    (hl : c ^ 2 * D ^ h ≤ X ^ 2 * D ^ rp) : P ^ (n * rm * (1 / q + vd / 2)) ≤ X := by
  have hD0 : 0 < D := hD ▸ Real.rpow_pos_of_pos hP0 _
  have hD1 : D ≤ 1 := hD ▸ Real.rpow_le_one hP0.le hP1 hvd
  have h0 : 0 < P ^ ((n * rm) / q) := Real.rpow_pos_of_pos hP0 _
  have h1 : D ^ (rp + rm') ≤ D ^ h := pow_le_pow_of_le_one hD0.le hD1 hh
  have h2 : c ^ 2 * D ^ rm' ≤ X ^ 2 := by
    have : c ^ 2 * D ^ rm' * D ^ rp ≤ X ^ 2 * D ^ rp := by
      calc c ^ 2 * D ^ rm' * D ^ rp = c ^ 2 * D ^ (rp + rm') := by ring
        _ ≤ c ^ 2 * D ^ h := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ ≤ _ := hl
    exact le_of_mul_le_mul_right this (pow_pos hD0 _)
  have h3 : (P ^ (n * rm * (1 / q + vd / 2))) ^ 2 = (P ^ ((n * rm) / q)) ^ 2 * D ^ rm' := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le,
      ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0, ← hrm]
    congr 1
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hP0 _).le hX two_ne_zero).1 ?_
  rw [h3]
  refine le_trans ?_ h2
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le (hcw.trans hc) 2) (pow_pos hD0 _).le

theorem colength_bound_linDat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t vd hvd rp rm W hW hW'
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast, zero_lt_iff, Ne, map_eq_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : v (algebraMap O C (p : O)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) fun h =>
      (Fact.out : ¬IsUnit (p : O)) (hv.isUnit_iff_valuation_eq_one.2 h)
  obtain ⟨-, -, α, b, hb⟩ := GlobalTheory.PlaceMono.place_monogenic p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  have hrm : ∀ τ ∈ Emb (O := O) w.bar,
      eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm := by
    intro τ hτ
    obtain ⟨W', hW''⟩ := hW' τ hτ
    have h1 := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rm ρG τ W' hW'').2.2
    have h2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG
      ((RingHom.mapMatrix (Int.castRingHom O)).comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp τ)).1
    rw [h1] at h2
    exact le_of_le_of_eq (Nat.le_add_left _ _) h2.symm
  obtain ⟨cw, hcw, hcwb⟩ := GlobalTheory.T.abelianPart_cokernel_length_le p C v O hv OE cp hU g H hL.noPad.1 hL.noPad.2 w t rm hrm
  obtain ⟨h, ψ, hh, hψ, f, hf⟩ := GlobalTheory.T.exists_abelian_torus_generators_at_place p C v O hv OE cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm
  obtain ⟨hinj, hvd0, hD⟩ := GlobalTheory.PowerBasisDiscr.discr_power_basis p C v O hv OE w t vd hvd α b hb
  obtain ⟨hex, hmono, hfp⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  have hres := fun j => GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rp ρG _ (W j) (hW j)
  have hstab : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), ∃ u' : Fin d → O, ∀ j,
      Pdiv.ChartF.res (W j) u' = tauExt ((t j : Emb (O := O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) u := by
    intro x u
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, fun j => by simp⟩
    | tmul c a =>
      refine ⟨algebraMap ℤ_[p] O c • ((ρG a)ᵀ *ᵥ u), fun j => ?_⟩
      rw [map_smul, (hres j).2.1, smul_smul]
      simp [tauExt, Algebra.ofId_apply]
    | add x y hx hy =>
      obtain ⟨u1, h1⟩ := hx
      obtain ⟨u2, h2⟩ := hy
      exact ⟨u1 + u2, fun j => by rw [map_add, h1, h2, map_add, add_smul]⟩
  let κ : (Fin d → O) →ₗ[O] (Fin w.n × Fin rp → O) :=
    LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))
  have hκa : ∀ u y, κ u y = Pdiv.ChartF.res (W y.1) u y.2 := fun u y => rfl
  have hMfg : (LinearMap.range κ).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hmem : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), (fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) x * κ u y) ∈ LinearMap.range κ := by
    intro x u
    obtain ⟨u', hu'⟩ := hstab x u
    refine ⟨u', funext fun y => ?_⟩
    rw [hκa, hκa, hu']
    rfl
  obtain ⟨c, hc⟩ := hex _ (lav_fp hfp (LinearMap.range κ)
    (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2))
    hMfg (Submodule.fg_span (Set.finite_range _)) (by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      have := hmem (α ^ (q.1 : ℕ)) (ψ q.2)
      simp only [map_pow] at this
      exact this))
  have hcc : cw ≤ c := hmono _ _ f cw c hf hcw hc
  have hcw0 : (0 : ℝ) < cw := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) hcwb
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hcw0) hcc : (0 : NNReal) < c).ne'
  obtain ⟨x, hx, hineq⟩ := GlobalTheory.T.lattice_inequality_valuation_integers C v O hv ⟨_, hp0, hp1⟩ w.n rp h
    (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) hinj (LinearMap.range κ) hMfg
    (by rintro _ ⟨u, rfl⟩; exact hmem α u)
    (by
      intro τ z
      obtain ⟨u, hu⟩ := (hres τ).1 z
      exact ⟨κ u, ⟨u, rfl⟩, fun i => by rw [hκa, hu]⟩)
    (fun l => κ (ψ l)) (fun l => ⟨ψ l, rfl⟩) c hc0 hc
  have hxs : ∀ j, ∃ y, HasLen v O ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) y ∧ x j ≤ y := by
    intro j
    have hle : Submodule.span O (Set.range fun l => fun i => κ (ψ l) (j, i)) ≤
        Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k)) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hψ l j
    obtain ⟨y, hy⟩ := hex ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k)))
      (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
    exact ⟨y, hy, hmono _ _ (Submodule.factor hle) _ _ (Submodule.factor_surjective hle) (hx j) hy⟩
  choose xs hxs1 hxs2 using hxs
  refine ⟨xs, hxs1, le_trans ?_ (Finset.prod_le_prod' fun j _ => hxs2 j)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine lav_num _ _ c cw _ _ _ _ _ rp rm h rfl (by exact_mod_cast hp0) (by exact_mod_cast hp1.le) hvd0 hD hh
    hcwb (by exact_mod_cast hcc) (NNReal.coe_nonneg _) ?_
  exact_mod_cast hineq

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalTorusCharacterLiftToLawStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalTorus_character_lift_to_law : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  first | exact @GlobalTheory.ChF.Lift.exists_char_lift | exact GlobalTheory.ChF.Lift.exists_char_lift | (intros; apply GlobalTheory.ChF.Lift.exists_char_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory

theorem nuLocC_le_nuPlE_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.DescentSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι k Y hY a n
  obtain ⟨hint, hval⟩ := GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι
  unfold FBChart.nuPlE
  refine le_iInf₂ ?_
  rintro x ⟨P, hP, f, hf, rfl⟩
  have hh : MvPowerSeries.constantCoeff (a3h C3) = 0 := by
    let _ := io.toAlgebra
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ C3.ch.gauge.ax0 0 fun _ => rfl
  unfold FBChart.nab
  rw [hY.h, hY.w0, hY.k]
  refine GlobalTheory.nabValN_lower_bound_baseChange T C V.v ι V.RR (fun x => Iff.rfl) hint _ (𝓞 E) (a3B C3) Y.B hY.F hY.act (a3h C3) hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) (nuLocC C3 (eOf T V) k a n) ?_ P hP f hf
  intro Q hQ g hg
  rw [← hval]
  unfold nuLocC
  exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOne
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

open Formalism.BaseCaseIdentities (Data Kn s0)

noncomputable section

namespace GlobalTheory.MainTerm

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem mm_neg_iff {x : C} : V.MM (-x) ↔ V.MM x := by
  unfold VF.MM
  rw [V.v.map_neg]

theorem chain_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) (s : ℕ) (hs : s < Kn i) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s * X.j' ∧
      IndepMod V (fun δ c => if D.lev c = s then chainMat D s c (em (cc δ)) else 0) := by
  haveI := X.algClosed
  induction s with
  | zero =>
    refine ⟨N, Function.Embedding.refl _, by omega, fun co _ hco ν => ?_⟩
    have := hco (em ν)
    simpa [hem, chainMat_zero] using this
  | succ s ih =>
    obtain ⟨m, cc, hm, hI⟩ := ih (by omega)
    have hsK : s < Kn D.i := by rw [h.2.2.1]; omega
    obtain ⟨m', cc', hm', hI'⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (I g) m X.j' (V.l ^ 2)
      (Nat.one_le_pow _ _ V.l_prime.pos)
      (fun δ c => if D.lev c = s + 1 then chainMat D (s + 1) c (em (cc δ)) else 0)
      (by
        intro δ c
        split_ifs
        · exact h.chainMat_int _ _ _
        · exact VF.Ge.zero 0)
      (by
        intro N' x hx hxI hxM
        refine GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal C V d I J X hA g a hb i S Z D h s hs m
          (fun δ c => chainMat D s c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI N' x hx hxI ?_
        intro ν e he
        have := hxM ν e
        simpa [he, chainMat_succ, hsK, h.2.1] using this)
    exact ⟨m', cc'.trans cc, by rw [Nat.succ_mul]; omega, hI'⟩

theorem mainVec_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s0 i * X.j' ∧
      IndepMod V (fun δ => mainVec S D (em (cc δ))) := by
  have hi : Odd i := h.2.2.1 ▸ D.i_odd
  obtain ⟨m, cc, hm, hI⟩ := chain_rank X hA g a hb i S D h N em hem (s0 i) (chainStartIndex_lt_chainLength_of_odd hi)
  refine ⟨m, cc, hm, fun co hco hM => ?_⟩
  refine GlobalTheory.T.independentMod_firstCoeff_chainLastStep C V d I J X hA g a hb i S Z D h (s0 i) (chainStartIndex_lt_chainLength_of_odd hi) m
    (fun δ c => chainMat D (s0 i) c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI co hco ?_
  intro κ
  have h1 := hM κ
  simp only [mainVec, h.2.2.1, h.2.1, chainStartIndex_lt_chainLength_of_odd hi, and_true] at h1
  rcases neg_one_pow_eq_or C (s0 i + 1) with h2 | h2
  · simpa [h2] using h1
  · rw [← mm_neg_iff]
    simpa [h2] using h1

theorem not_big_add_odd (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) {i : ℕ} (hi : Odd i) : ¬ X.big g (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    obtain ⟨e, he⟩ := hA.1
    have h2 : 2 ∣ d := ⟨e, by omega⟩
    have h3 : (a + (i : ZMod d)).val % 2 = (a.val + i) % 2 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2, Nat.add_mod,
        Nat.mod_mod_of_dvd _ h2, ← Nat.add_mod]
    obtain ⟨k, rfl⟩ := hi
    simp only [Nat.even_iff]
    omega
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · rw [hA.2, hpar, not_not]; exact (hA.2 a).1 hb
  · rw [h1, not_not, hA.2, hpar, ← hA.2]; exact (h1 a).1 hb

theorem both (X : RowData C V d I J) (hA : X.Alt) (h5 : 5 ≤ V.l) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d) (U : Fin X.n → I g → C)
    (U' : Fin X.n → I (1 - g) → C) (hU : X.SatIn g a U)
    (hU' : X.SatIn (1 - g) (a + (i : ZMod d)) U') :
    ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
      X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ ∧
        (i = 1 → X.MPlusConcl g a n0 e v' Φ) := by
  haveI := X.algClosed
  haveI := X.charZero
  obtain ⟨S, N1, D, hv, hl, hDi, hal, hty, hN1, A, hAint, hAeq⟩ :=
    GlobalTheory.T.rowData_adaptedChainData C V d I J X hA g a hb i hi hid U hU
  have h : Adapted S D a i := ⟨hv, hl, hDi, hal, hty⟩
  obtain ⟨m, c1, hm, hI1⟩ := mainVec_rank X hA g a hb i S D h N1 ⟨D.ι, D.ι_inj⟩ D.ι_lev
  have hΨint : ∀ c0 (u : I (1 - g) → C), (∀ k, V.Ge 0 (u k)) →
      V.Ge 0 (∑ κ : J g, ∑ k : I (1 - g), mainVec S D c0 κ * X.pair g κ k * u k) :=
    fun c0 u hu => VF.Ge.sum fun κ _ => VF.Ge.sum fun k _ =>
      ((h.mainVec_int c0 κ).mul_int (X.pair_int g κ k)).mul_int (hu k)
  obtain ⟨n0, c2, hn0, hI2⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (Fin X.n) m X.j 1 le_rfl
    (fun δ b => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (D.ι (c1 δ)) κ * X.pair g κ k * U' b k)
    (fun δ b => hΨint _ _ (hU'.1.1 b))
    (by
      intro N x hx hxI hxM
      refine GlobalTheory.T.pairing_kernel_le_of_saturated_submodule C V d I J X g _ (not_big_add_odd X hA g a hb hi) U' hU' N
        (fun ν κ => ∑ δ, x ν δ * mainVec S D (D.ι (c1 δ)) κ)
        (fun ν κ => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (h.mainVec_int _ _)) ?_ ?_ ?_
      · intro ν κ hκ
        simp [h.mainVec_pure _ κ hκ]
      · intro co hco hM
        refine hxI co hco (hI1 (fun δ => ∑ ν, co ν * x ν δ)
          (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) fun κ => ?_)
        convert hM κ using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      · intro ν b
        convert hxM ν b using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, pow_one]
        rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_comm)
  let em : Fin n0 ↪ I g := (c2.trans c1).trans ⟨D.ι, D.ι_inj⟩
  have hem : ∀ δ, D.lev (em δ) = 0 := fun δ => D.ι_lev _
  have hK : 0 < Kn i := by rw [Kn_eq hi]; omega
  have hemty : ∀ δ, (X.G g).ty (Sum.inl (em δ)) = a := fun δ => by
    rw [hty _ (by rw [hem]; exact hK), hem]; simp
  have hemal : ∀ δ x, S.al (em δ) 1 x = 0 := fun δ x =>
    h.al_one (D.pure_good _ (by rw [hem, hDi]; exact hK)) x
  obtain ⟨hn0n, Y, hYint, hYdet, hYΦ⟩ := GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal C V X.n n0
    (fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (em c) κ * X.pair g κ k * U' b k)
    (fun b c => hΨint _ _ (hU'.1.1 b)) hI2
  let v' : Fin X.n → I (1 - g) → C := fun b x => ∑ b', Y b b' * U' b' x
  have hv'int : ∀ b k, V.Ge 0 (v' b k) := fun b k =>
    VF.Ge.sum fun b' _ => (hYint b b').mul_int (hU'.1.1 b' k)
  have hv'ty : ∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0 :=
    fun b k hk => by simp [v', hU'.2 _ k hk]
  have hety : ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → S.tan (em c) x = 0 := fun c x hx =>
    tan_pure S _ x (by rw [hemty]; exact hx)
  have hS0 : ∀ g', Nonempty (Sys (X.G g')) := fun g' => by
    obtain ⟨S', -⟩ := sysExists (X.G g') (fun c x => if c = x then 1 else 0)
      (by intro c x; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0])
      (by
        intro c x hx
        rw [if_neg]
        rintro rfl
        exact hx rfl)
      (by
        have : (Matrix.of fun c x : I g' => if c = x then (1 : C) else 0) = 1 := by
          ext c x; simp [Matrix.one_apply]
        rw [this, Matrix.det_one, V.v.map_one])
    exact ⟨S'⟩
  obtain ⟨SS, rfl⟩ : ∃ SS : ∀ g', Sys (X.G g'), SS g = S :=
    ⟨Function.update (fun g' => (hS0 g').some) g S, by simp⟩
  choose t ht using fun g' => (tExistsUnique (X.G g') (SS g')).exists
  have hζ := GlobalTheory.T.zetaSeries_leaf_mainTerm_curveSystem C V d (I g) (J g) (X.G g) (SS g) _ D a i h hid (t g) (ht g) n0 em hem
  refine ⟨n0, fun δ => (SS g).tan (em δ), v',
    fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec (SS g) D (em c) κ * X.pair g κ k * v' b k,
    ⟨⟨?_, hn0n⟩, isSat_tan _ em, ⟨fun c => A (c1 (c2 c)), fun c b => hAint _ b, fun c x => ?_⟩,
      ⟨Y, hYint, hYdet, fun b x => rfl⟩, fun b c => hΨint _ _ (hv'int b), fun b c hb => ?_, ?_,
      fun μ hμ => GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis C V d I J X g a i _ _ _ _ _ μ hμ⟩,
    ⟨SS g, t g, em, fun c => mainVec (SS g) D (em c), ht g, fun c => rfl, hemal,
      fun c κ => h.mainVec_int _ _, fun b c => rfl, hζ⟩, ?_⟩
  · have h1 := two_mul_chainStartIndex_add_one_of_odd hi
    rw [Kn_eq hi] at hN1
    have h2 : (i + 1) * X.j' = (s0 i + 1 + 1) * X.j' + s0 i * X.j' := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · exact ((SS g).cur_zero_inl _ x).symm.trans (hAeq _ x)
  · rw [← hYΦ b c hb]
    simp only [v', Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin X.n))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact GlobalTheory.T.weight_gauge_sub_mainTerm_leaf C V d I J X hA h5 g a i hi hid SS t ht n0 X.n _ v'
      (fun c => mainVec (SS g) D (em c)) hety hv'int hv'ty
      (GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData C V d (I g) (J g) (X.G g) (SS g) _ D a i h (t g) (ht g) n0 em hem) hζ
  · rintro rfl
    simp only [fun c => funext (h.mainVec_level_one (hem c))]
    exact GlobalTheory.T.gauge_sub_mainTerm_integral_lowBidegree C V d I J X hA hid g a SS t ht n0 em v' hemty hemal hv'int hv'ty

theorem main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  intro C _ V d _ I J _ _ X
  constructor
  · intro hA h5 g a hb i hi hid U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, -⟩ := both X hA h5 g a hb i hi hid U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2⟩
  · intro hA h5 hd g a hb U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, h3⟩ := both X hA h5 g a hb 1 odd_one hd U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2, h3 rfl⟩

end GlobalTheory.MainTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SmoothOfRelativeDimensionOfGrpPullbackLocalRingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing : ∀ (R' O : Type) [CommRing R'] [IsLocalRing R'] [CommRing O] [Nontrivial O] (π : R' →+* O) (G : Over (Spec (CommRingCat.of R'))) [GrpObj G] (G' : Over (Spec (CommRingCat.of O))) [GrpObj G'] (ψ : G'.left ⟶ G.left) (g : ℕ), IsAbelianScheme G → Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom π)) ψ → SmoothOfRelativeDimension g G'.hom → SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback | exact GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback | (intros; apply GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback <;> assumption)
end

