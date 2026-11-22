import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PushLettersIntCastOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology

namespace GlobalTheory.RationalDiscrete

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nhds_zero_inclR :
    ∃ U ∈ 𝓝 (0 : AF F ⊗[F] E), ∀ x : E, inclR (F := F) (AF F) x ∈ U → x = 0 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop (F := F) (E := E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
  refine ⟨⋂ k, B.coord k ⁻¹' U, Filter.iInter_mem.2 fun k => ?_, fun x hx => ?_⟩
  · exact (hc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  · refine b.ext_elem fun k => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine h _ ?_
    have hk : B.repr ((1 : AF F) ⊗ₜ[F] x) k ∈ U := Set.mem_iInter.1 hx k
    rw [Algebra.TensorProduct.basis_repr_tmul] at hk
    simpa using hk

theorem discreteTopology_HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    DiscreteTopology (HFinIn (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : HFinIn (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : HFinIn (AF F) σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin M) (Fin M) E) - 1 : Matrix (Fin M) (Fin M) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discreteTopology_GQ : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) :=
  fun D V => discreteTopology_HFinIn D.sp.cm.sig V.gram

end GlobalTheory.RationalDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraphStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinSeries_term_unitary_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  first | exact @GlobalTheory.SW.eisTerm_graph | exact GlobalTheory.SW.eisTerm_graph | (intros; apply GlobalTheory.SW.eisTerm_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Letters

theorem rename_place_mem {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ}
    (hP : P ∈ Harm.rowHighest R c c') :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' := by
  obtain ⟨h₁, h₂, h₃⟩ := Harm.mem_rowHighest_iff_rowAdd.1 hP
  set F := f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ)) with hF
  have hFa (t : T) (v : (Fin p ⊕ Fin q) × κ) : F (t, v) = (f t, v) := rfl
  refine Harm.mem_rowHighest_iff_rowAdd.2 ⟨fun t a b => ?_, fun t ρ => ?_, fun t ρ ρ' hρ s => ?_⟩ <;>
    obtain ⟨t, rfl⟩ := f.surjective t
  · have := congrArg (MvPolynomial.rename F) (h₁ t a b)
    rw [map_zero, Harm.laplacian_apply, map_sum] at this
    rw [Harm.laplacian_apply, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Harm.xVar, Harm.yVar, ← hFa, ← hFa, MvPolynomial.pderiv_rename F.injective,
      MvPolynomial.pderiv_rename F.injective]
  · rw [Harm.isWeightedHomogeneous_rename_iff F.injective, h, h']
    convert h₂ t ρ using 1
    funext ⟨t', ρ', k⟩
    simp [hFa, Harm.rowInd_apply]
  · conv_rhs => rw [← h₃ t ρ ρ' hρ s]
    refine DFunLike.congr_fun (?_ : (Harm.rowAdd (f t) ρ ρ' (s : R)).comp (MvPolynomial.rename F) =
      (MvPolynomial.rename F).comp (Harm.rowAdd t ρ ρ' (s : R))) P
    refine MvPolynomial.algHom_ext fun ⟨t', ρ'', k⟩ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, hFa, Harm.rowAdd_X, Harm.rowAdd_X]
    simp only [f.injective.eq_iff]
    split_ifs <;> simp [hFa]

theorem rename_place_mem_iff {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ} :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' ↔
      P ∈ Harm.rowHighest R c c' := by
  refine ⟨fun hP => ?_, rename_place_mem f h h'⟩
  have := rename_place_mem f.symm (d := c) (d' := c') (fun t => by rw [← h, f.apply_symm_apply])
    (fun t => by rw [← h', f.apply_symm_apply]) hP
  rw [MvPolynomial.rename_rename] at this
  convert this
  rw [show (f.symm.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) ∘
    (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) = id from
      (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))).symm_comp_self, MvPolynomial.rename_id_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem exists_isSympl (X : Data E r) (hL : SelfD X X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) :
    ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ, IsSympl X bas := by
  obtain ⟨h1, h2, h3⟩ := ThetaHol.finrank_lattice X
  have hg : g = X.Ψ.card * r := by simpa using Fintype.card_congr idx
  have hκ : X.κ0 / 2 ≠ 0 := by rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  have hlat : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  obtain ⟨B, hB⟩ : ∃ B : LinearMap.BilinForm ℚ (Fin r → E), ∀ u v, EF X u v = B u v :=
    ⟨_, TensLat.EF_eq_bilin X⟩
  choose k hk using fun u v : X.Λ => (hL.2 u).1 u.2 v v.2
  have hk' (u v : X.Λ) : (k u v : ℚ) = B u v := (hk u v).symm.trans (hB _ _)
  let β : LinearMap.BilinForm ℤ X.Λ := LinearMap.mk₂ ℤ k
    (fun x x' y => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
    (fun x y y' => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
  have hβ (u v : X.Λ) : (β u v : ℚ) = EF X u v := (hk u v).symm
  have halt : β.IsAlt := fun x => by
    have := TensLat.EF_swap X x x
    apply Int.cast_injective (α := ℚ)
    rw [hβ, Int.cast_zero]
    linarith
  have hbij : Function.Bijective β := by
    constructor
    · intro x x' h
      refine Subtype.ext (eq_of_EFf_eq hκ X.Gm_det hlat fun y hy => ?_)
      exact (hβ x ⟨y, hy⟩).symm.trans (h ▸ hβ x' ⟨y, hy⟩)
    · intro φ
      obtain ⟨x, hx, hφ⟩ := exists_traceFormDual_eq hκ X.Gm_det hlat φ.toAddMonoidHom
      refine ⟨⟨x, (hL.2 x).2 hx⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
      exact (hβ _ _).trans (hφ y).symm
  obtain ⟨g', bas, S, hs, -, hr⟩ := exists_symplectic_coordinates_adapted halt hbij (I := ⊥)
    (fun m x hm hx => by simpa [hm] using hx) (by simp) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  exact ⟨bas, fun a b => by rw [← hβ, hs]; simp⟩

end GlobalTheory.Dict.Letters

open GlobalTheory.Dict.Letters GlobalTheory.Harm in

theorem GlobalTheory.Dict.exists_dic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  intro E _ _ _ H Dw l c σ r g n X a e hσ hr hp0 hΨ hL hD
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hr' : X.p0 + Dw.p = r := by omega
  have i1 := ComplexEmbedding.involutive_conjugate E
  have i2 : ∀ τ, ¬ InPsi H τ ↔ InPsi H (ComplexEmbedding.conjugate τ) := not_mem_hostType_iff H
  have i3 : ∀ τ, InPsi H τ → Dw.mult τ = Dw.p := fun _ => mult_of_mem Dw
  have i4 : ∀ τ, InPsi H τ → Dw.mult (ComplexEmbedding.conjugate τ) = X.p0 := fun _ h =>
    (mult_conjEmb_of_mem Dw h).trans hp0.symm
  let f : {τ // InPsi H τ} ≃ X.Ψ := (Equiv.ofBijective _ hbij).subtypeEquiv fun τ =>
    ((hΨ _).trans (hrt τ)).symm
  have hf (t : {τ // InPsi H τ}) : (f t).1 = relab c σ t.1 := rfl
  let ρ : Lt1 Dw ≃ X.Ψ × (Fin Dw.p ⊕ Fin X.p0) :=
    (halfRowEquiv i1 i2 i3 i4).trans (f.prodCongr (Equiv.refl _))
  let idx : Fin g ≃ X.Ψ × Fin r := e.trans (ρ.trans (rowOf X hr'))
  have hidx (j) : (∃ t : {τ // InPsi H τ}, ∃ i : Fin Dw.p, (e j).1 = t.1 ∧ ((e j).2 : ℕ) = i ∧
      idx j = (f t, rowIdx hr' (Sum.inl i))) ∨
      ∃ t : {τ // InPsi H τ}, ∃ i : Fin X.p0, (e j).1 = ComplexEmbedding.conjugate t.1 ∧ ((e j).2 : ℕ) = i ∧
        idx j = (f t, rowIdx hr' (Sum.inr i)) := by
    obtain ⟨⟨t, i | i⟩, h⟩ := (halfRowEquiv i1 i2 i3 i4).symm.surjective (e j)
    · refine Or.inl ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
    · refine Or.inr ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
  obtain ⟨bas, hbas⟩ := exists_isSympl X hL idx
  let k₀ : {τ // InPsi H τ} → Fin Dw.p → ℕ := fun t => diffOf fun i => a (t.1, i)
  let k₀' : {τ // InPsi H τ} → Fin X.p0 → ℕ := fun t => diffOf fun i => a (ComplexEmbedding.conjugate t.1, i)
  have hx (t) : partOf (k₀ t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  have hy (t) : partOf (k₀' t) = fun i : Fin X.p0 => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  let eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n) :=
    (typeLetterEquiv i1 i2 i3 i4 n).trans (f.prodCongr (Equiv.refl _))
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        MvPolynomial.rename eL P ∈ rowHighest c.F (k₀ ∘ f.symm) (k₀' ∘ f.symm) := by
    rw [Equiv.coe_trans, ← MvPolynomial.rename_rename,
      rename_place_mem_iff f (c := k₀) (c' := k₀') (fun t => by simp) (fun t => by simp)]
    simp only [mem_HHa_iff_rename i1 i2 i3 i4, mem_rowHighest_iff_rowAdd, hx, hy]
  have hinv (τ) : Function.invFun (relab c σ) (relab c σ τ) = τ := Function.leftInverse_invFun hbij.1 τ
  refine ⟨⟨hr', bas, idx, hbas, e, eL, k₀ ∘ f.symm, k₀' ∘ f.symm, fun x v j => ?_, fun j => ?_,
    fun ℓ => ?_, ?_, fun P hP => ?_, ?_⟩, rfl, fun hpos hp => ?_⟩
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · have hi := i.isLt
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_le _ _ _ _ (by simp), perFr,
        dif_pos (show relab c σ t.1 ∈ X.Ψ from (f t).2), dif_pos (by omega)]
      rfl
    · have hi := i.isLt
      have h4 : relab c σ (ComplexEmbedding.conjugate t.1) = ComplexEmbedding.conjugate (f t).1 := hcj t.1
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_lt _ _ _ _ (by rw [rowIdx_inr]; omega), h4]
      have h5 : rowIdx hr' (Sum.inr i) = ⟨X.p0 - 1 - i, by omega⟩ := Fin.ext (rowIdx_inr hr' i)
      rw [h5]
      generalize f t = u
      obtain ⟨τ, hτ⟩ := u
      obtain ⟨τ, rfl⟩ := i1.surjective τ
      rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from i1 τ, perFr,
        dif_neg (fun h => (X.cmType τ).1 h hτ), dif_pos (show conjEmb τ ∈ X.Ψ from hτ), dif_pos (by omega)]
      rfl
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · rw [h3, h1]
      exact rowType_rowOf_inl X hr' (f t) i
    · rw [h3, h1]
      exact (rowType_rowOf_inr X hr' (f t) i).trans (hcj t.1).symm
  · have : idx.symm (rowOf X hr' ((eL ℓ).1, (eL ℓ).2.1)) = e.symm ⟨ℓ.1, ℓ.2.1⟩ := by
      rw [Equiv.symm_apply_eq]
      simp only [idx, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    rw [letterDir, this]
    rfl
  · funext τ j
    obtain ⟨t, rfl⟩ := f.surjective τ
    obtain ⟨i | i, rfl⟩ := (rowIdx hr').surjective j
    · rw [wtOf_inl, wtX, if_pos (by simp), hf, hinv, Function.comp_apply, f.symm_apply_apply, hx]
      simp
    · have hi := i.isLt
      rw [wtOf_inr, wtX, if_neg (by rw [rowIdx_inr]; omega), hf, ← hcj, hinv, Function.comp_apply,
        f.symm_apply_apply, hy, rowIdx_inr, show X.p0 - 1 - (X.p0 - 1 - i) = i by omega]
      rfl
  · rw [← MvPolynomial.map_rename]
    exact map_mem_rowHighest _ ((hmem P).1 hP)
  · letI := σ.toAlgebra
    rw [← span_map_rowHighest c.F ℂ]
    refine Submodule.span_mono ?_
    rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨P, rfl⟩ := MvPolynomial.rename_surjective _ eL.surjective Q
    exact ⟨P, (hmem P).2 hQ, (MvPolynomial.map_rename _ _ _).symm⟩
  · obtain ⟨t⟩ : Nonempty {τ // InPsi H τ} := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : InPsi H τ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, (i2 τ).1 h⟩⟩
    refine ⟨f t, ⟨Dw.p - 1, by omega⟩, by simp only; omega, ?_⟩
    have := hpos t.1 t.2 (by rw [i3 _ t.2]; exact hp)
    rw [i3 _ t.2] at this
    simp only [Function.comp_apply, Equiv.symm_apply_apply, k₀, diffOf]
    rw [dif_neg (by omega)]
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NotIsIsoOfDefinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspClass

private theorem hermC_mulVec_mulVec_eq_sum_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P *ᵥ w) (P *ᵥ w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by
  simp only [FD.hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem not_isIso_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hξ0, hne⟩
  have τ0 : E →+* ℂ := Classical.choice inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · exact ⟨_, not_not.mp (mt (X.cmType τ0).mpr h)⟩
  obtain ⟨P, hPdet, hP⟩ := X.signature ⟨τ, hτ⟩
  have hherm : FD.hermC τ X.Gm (fun a => τ (ξ a)) (fun a => τ (ξ a)) = 0 := by
    have h1 := congrArg τ hξ0
    rw [map_zero] at h1
    rw [← h1]
    simp [FD.herm, FD.hermC, FD.cc, map_sum, map_mul, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨w, hw⟩ : ∃ w, P *ᵥ w = fun a => τ (ξ a) :=
    ⟨P⁻¹ *ᵥ (fun a => τ (ξ a)), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mulVec]⟩
  have hsum : ∑ a, ((Complex.normSq (w a) : ℝ) : ℂ) = 0 := by
    rw [← hherm, ← hw, hermC_mulVec_mulVec_eq_sum_gram, hP]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [Matrix.diagonal_apply_eq, FD.sgn, h0, Complex.mul_conj]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  have hsum' : ∑ a, Complex.normSq (w a) = 0 := by exact_mod_cast hsum
  have hw0 : w = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg (w a))).mp hsum' a
      (Finset.mem_univ a)
    simpa using this
  apply hne
  funext a
  have := congrFun hw a
  rw [hw0, Matrix.mulVec_zero] at this
  exact (map_eq_zero τ).mp this.symm

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → r ≤ n → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk hrn φ hφ P hP Q hQ hΓ
  obtain ⟨-, hlink⟩ := GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn
  obtain ⟨m, a, b, t, hab⟩ := hlink φ hφ
  refine GlobalTheory.ThFr.mem_SS_of_eq_sum_thFr (idx := idx) (hr := hr) (s := Finset.univ) (t := t)
    (a := fun j k i => (a j k i : ℝ)) (b := fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ?_
    (fun _ _ => hP) ?_ hΓ
  · rcases hk with ⟨τ, i, hi, hki⟩ | hq
    · exact Or.inl ⟨by omega, τ, Or.inl ⟨i, hi, hki⟩⟩
    · exact Or.inr (not_isIso_of_definite X (by omega))
  · intro x hx
    exact (hQ x hx).trans (hab P x hx)

end GlobalTheory.Dict.CuspClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighestStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceKernel_holomorphic_weight_rowHighest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → ∀ x₂ ∈ X.dom, DifferentiableOn ℂ (fun x₁ => kern X hr idx P x₁ x₂) X.dom ∧ ∀ x₁ ∈ X.dom, ∀ b ∈ Bor X.Ψ r, kern X hr idx P (rmul x₁ b) x₂ = bchar (wtOf X hr c c' n) b * kern X hr idx P x₁ x₂ := by
  first | exact @GlobalTheory.KernHol.kern_hol_weight | exact GlobalTheory.KernHol.kern_hol_weight | (intros; apply GlobalTheory.KernHol.kern_hol_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeriesStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ (a b : Fin n → Fin g → ℚ), ∃ φ : TF n g, IsSB φ ∧ (∀ m : Matrix (Fin n) (Fin g) ℚ, φ m = if ∀ k i, IsIntegral ℤ (m k i - a k i) then cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ)) else 0) ∧ ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = thFr X hr bas idx n (fun k i => (a k i : ℝ)) (fun k i => (b k i : ℝ)) P x) ∧ ∀ φ : TF n g, IsSB φ → ∃ (m : ℕ) (a b : Fin m → Fin n → Fin g → ℚ) (t : Fin m → ℂ), ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = ∑ j, t j * thFr X hr bas idx n (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x := by
  first | exact @GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | exact GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | (intros; apply GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic <;> assumption)
end

