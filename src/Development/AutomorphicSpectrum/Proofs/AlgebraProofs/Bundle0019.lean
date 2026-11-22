import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLattice
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem afQuot_equiv_coords : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) :=
  PositivityTheory.HtPt.Rh.afquot

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_ideal_principal_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.eig_rank_one | exact GlobalTheory.CompanionTheory.Ar.GR.eig_rank_one | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.eig_rank_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmProjectiveModulePairingP
section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.TwGenus

theorem two_unimodular_isometric_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v :=
  @PositivityTheory.UnitarySelfGeneration.tw_g_padic

end GlobalTheory.CompanionTheory.TwGenus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotient
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg

theorem det_adapted {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V)
    {m n : ℕ} (bW cW : Module.Basis (Fin m) K W) (bQ cQ : Module.Basis (Fin n) K (V ⧸ W))
    (b c : Module.Basis (Fin (m + n)) K V)
    (hb1 : ∀ j, b (Fin.castAdd _ j) = bW j) (hb2 : ∀ j, W.mkQ (b (Fin.natAdd _ j)) = bQ j)
    (hc1 : ∀ j, c (Fin.castAdd _ j) = cW j) (hc2 : ∀ j, W.mkQ (c (Fin.natAdd _ j)) = cQ j) :
    b.det c = bW.det cW * bQ.det cQ := by
  have h1 : ∀ (i : Fin m) (x : W), b.repr (x : V) (Fin.castAdd _ i) = bW.repr x i := by
    intro i x
    have : (b.coord (Fin.castAdd _ i)).comp W.subtype = bW.coord i := by
      refine bW.ext fun j => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
        ← hb1, Module.Basis.repr_self, Finsupp.single_apply, Fin.castAdd_inj]
    exact LinearMap.congr_fun this x
  have h2 : ∀ (i : Fin n) (x : V), b.repr x (Fin.natAdd _ i) = bQ.repr (W.mkQ x) i := by
    intro i x
    have : b.coord (Fin.natAdd _ i) = (bQ.coord i).comp W.mkQ := by
      refine b.ext fun j => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have h0 : W.mkQ (b (Fin.castAdd n j)) = 0 := by
          rw [hb1]; simp
        have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, h0, map_zero,
          Module.Basis.repr_self, Finsupp.single_apply, hne, if_false, Finsupp.coe_zero,
          Pi.zero_apply]
      · simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb2,
          Module.Basis.repr_self, Finsupp.single_apply, Fin.natAdd_inj]
    exact LinearMap.congr_fun this x
  have key : (b.toMatrix c).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (bW.toMatrix cW)
        (Matrix.of fun i j => b.repr (c (Fin.natAdd _ j)) (Fin.castAdd _ i)) 0
        (bQ.toMatrix cQ) := by
    ext (i | i) (j | j)
    · simp [Module.Basis.toMatrix_apply, hc1, h1]
    · simp [Module.Basis.toMatrix_apply]
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Module.Basis.toMatrix_apply, hc1, h2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (cW j).2]
      simp
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        Module.Basis.toMatrix_apply, hc2, h2, Matrix.fromBlocks_apply₂₂]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁]

theorem deg_eq_subDeg_add_deg_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
    (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hex := fun i => (hL.1 i).elim fun b hb => GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
  choose bW bQ b hb hbW hbQ h1 h2 using hex
  obtain ⟨hS, hQ⟩ := GlobalTheory.T.sub_and_quotient_bundles K C V L W hL
  obtain ⟨-, eL⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (b i₀) b hL hb
  obtain ⟨fS, eS⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C W (sub C L W) _ (bW i₀) bW hS hbW
  obtain ⟨fQ, eQ⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (V ⧸ W) (quot C L W) _ (bQ i₀) bQ hQ hbQ
  rw [subDeg, eL, eS, eQ, ← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    rw [det_adapted W (bW i₀) (bW i) (bQ i₀) (bQ i) (b i₀) (b i) (h1 i₀) (h2 i₀) (h1 i) (h2 i),
      map_mul, WithZero.log_mul, mul_add]
    · exact (C.v i).ne_zero_iff.2 ((bW i₀).isUnit_det (bW i)).ne_zero
    · exact (C.v i).ne_zero_iff.2 ((bQ i₀).isUnit_det (bQ i)).ne_zero
  · refine fS.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]
  · refine fQ.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem apply_of_mem_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {x : V}
    (hx : x ∈ eigSp ρ σ) (a : 𝓞 E) : ρ a x = σ (a : E) • x := by
  have := (Submodule.mem_iInf _).1 hx a
  simpa [sub_eq_zero] using this

theorem sum_smul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {N : ℕ} (t : Fin N → V)
    (y : Fin N → K) :
    ∑ i, y i • eigProj ρ σ (t i) =
      ∑ q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
        (y q.1 * σ (dualInt E q.2)) • ρ (RingOfIntegers.basis E q.2) (t q.1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eigProj, LinearMap.sum_apply, Finset.smul_sum, mul_smul]

omit [Algebra A K] [IsScalarTower A K V] in
theorem mem_of_isFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V)
    (h : IsFreeOn ρ X t) (i : Fin N) : t i ∈ X := by
  have h1 : t i = ∑ k, (RingOfIntegers.basis E).repr 1 k • ρ (RingOfIntegers.basis E k) (t i) := by
    have := congrArg (fun a => ρ a (t i)) ((RingOfIntegers.basis E).sum_repr 1)
    simp only [map_sum, map_zsmul, map_one, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    exact this.symm
  rw [h1, h.2.2]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine zsmul_mem ?_ _
  exact Submodule.subset_span ⟨(i, k), rfl⟩

theorem eigSub_eq_different_smul_eigQuot : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) (N : ℕ) (t : Fin N → V) (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → IsFreeOn ρ X t → (∀ x, x ∈ eigQuot ρ σ X ↔ d • x ∈ eigSub ρ σ X) ∧ eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) ∧ LinearIndependent K (fun i => eigProj ρ σ (t i)) ∧ Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
  intro A K _ _ _ _ V _ _ _ _ E _ _ ρ X N t σ d hinj hσ hd hX
  obtain ⟨he1, he2, -, he4⟩ := ProjEig.eigProj_spec K V E ρ σ
  obtain ⟨hd0, hd1, u, hu⟩ := GlobalTheory.T.different_generator_dual_integral A K E σ d hinj hσ hd
  have hQ : eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) := by
    apply le_antisymm
    · unfold eigQuot
      rw [hX.2.2, Submodule.map_span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨a, ha⟩ := hσ (RingOfIntegers.basis E k)
      have : eigProj ρ σ (ρ (RingOfIntegers.basis E k) (t i)) = a • eigProj ρ σ (t i) := by
        rw [← Module.End.mul_apply, he4, Module.End.mul_apply,
          apply_of_mem_eigSp ρ σ (he1 _), ← ha, IsScalarTower.algebraMap_smul]
      simp only [LinearMap.restrictScalars_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, mem_of_isFreeOn ρ X t hX i, rfl⟩
  have hli : LinearIndependent K (fun i => eigProj ρ σ (t i)) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy i
    rw [sum_smul_eigProj] at hy
    have h0 := Fintype.linearIndependent_iff.1 hX.1 _ hy
    calc y i = y i * ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) := by
          rw [hu, mul_one]
      _ = ∑ k, algebraMap A K (u k) * algebraMap A K d * (y i * σ (dualInt E k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          have := h0 (i, k)
          simp only at this
          rw [this, mul_zero]
  have hsp : Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he1 _
    · intro x hx
      rw [← he2 x hx]
      have hx' : x ∈ Submodule.span K (X : Set V) := by rw [hX.2.1]; trivial
      have : (Submodule.span K (X : Set V)).map (eigProj ρ σ) ≤
          Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) := by
        rw [Submodule.map_span_le]
        intro m hm
        apply Submodule.span_le_restrictScalars A K
        rw [← hQ]
        exact ⟨m, hm, rfl⟩
      exact this ⟨x, hx', rfl⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hQ, hli, hsp⟩
  · refine ⟨?_, ?_⟩
    · rw [hQ, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      have : d • ∑ i, c i • eigProj ρ σ (t i) =
          ∑ i, (algebraMap A K (c i) * algebraMap A K d) • eigProj ρ σ (t i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_mul, IsScalarTower.algebraMap_smul, mul_comm, mul_smul]
      rw [this, sum_smul_eigProj, hX.2.2]
      refine Submodule.sum_mem _ fun q _ => ?_
      obtain ⟨a, ha⟩ := hd1 q.2
      rw [mul_assoc, ← ha, ← map_mul, IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := hx
      exact Submodule.smul_mem _ d (show _ ∈ (eigSp ρ σ).restrictScalars A from he1 m)
  · obtain ⟨hx1, hx2⟩ := hx
    have hxe : x ∈ eigSp ρ σ := by
      have h2 : algebraMap A K d • x ∈ eigSp ρ σ := by
        rw [IsScalarTower.algebraMap_smul]; exact hx2
      exact (Submodule.smul_mem_iff _ hd0).1 h2
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hxe
    obtain ⟨y, rfl⟩ := hxe
    have hx1' : d • ∑ i, y i • eigProj ρ σ (t i) ∈ X := hx1
    rw [hX.2.2, Submodule.mem_span_range_iff_exists_fun] at hx1'
    obtain ⟨c, hc⟩ := hx1'
    have h3 : d • ∑ i, y i • eigProj ρ σ (t i) =
        ∑ i, (y i * algebraMap A K d) • eigProj ρ σ (t i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, IsScalarTower.algebraMap_smul]
    rw [h3, sum_smul_eigProj] at hc
    have h4 : ∀ q, algebraMap A K (c q) = y q.1 * algebraMap A K d * σ (dualInt E q.2) := by
      refine Fintype.linearIndependent_iffₛ.1 hX.1 _ _ ?_
      rw [← hc]
      exact Finset.sum_congr rfl fun q _ => IsScalarTower.algebraMap_smul _ _ _
    rw [hQ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h5 : y i = algebraMap A K (∑ k, u k * c (i, k)) := by
      rw [map_sum, ← mul_one (y i), ← hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, h4]
      ring
    rw [h5, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbation
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem frame_congr_posDef_on_places : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef :=
  @PositivityTheory.Xgf.exists_integral_posDef_perturbation

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem affine_mono (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  have := H.mono S φ φ' (by rw [← hφ, ← hφ', Category.assoc, Category.assoc, hab])
  rw [← cancel_epi j, hφ, hφ', this]

theorem affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

theorem affine_one (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩

theorem affine_inv (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this

theorem mono_of_isFinFlatSub (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this

theorem grpObj_of_isFinFlatSub (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariants
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem genAF_of_map_eq_invFun : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K :=
  PositivityTheory.HtPt.Rh.sub_pull

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharacters
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem addChar_mem_hopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier :=
  @PositivityTheory.HtPt.Ra.charmem

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionIdStatement
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_induction_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_scalar_extension : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | exact GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change <;> assumption)
end

