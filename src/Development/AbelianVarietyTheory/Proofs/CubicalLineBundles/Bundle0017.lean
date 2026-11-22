import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.Bundle0009
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundOfCoefficientBound
section
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmLowerBound_of_coeffBound :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hLK hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (MvPolynomial.coeff μ G * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CurveHomExtOfDerivativeLieBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomUnique

theorem hom_ext_of_lieBasis : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P Q : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (f f' : P.A ⟶ Q.A), (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom f → IsMonHom f' → v ≫ f = v ≫ f' → f = f' := by
  intro hU hB k _ s P Q v f f' hv hf hf' h
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB s P
  obtain ⟨Q', ψ, hQ⟩ := exists_isPolFibre hB s Q
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hP.2.1.1 v
  obtain ⟨g, hg, eg⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f
  obtain ⟨g', hg', eg'⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f'
  have hb := hv ℂ s P' φ v' hP hv'
  have e₁ : v' ≫ g = v' ≫ g' := by
    refine Over.OverMorphism.ext (hQ.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have hl : v.left ≫ f.left = v.left ≫ f'.left := congrArg (fun z => z.left) h
    unfold IsVecOver at hv'
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, eg, eg', ← Category.assoc, ← Category.assoc,
      hv', Category.assoc, Category.assoc, hl]
  have e₂ : g = g' := by
    refine (HomDescent.pol_countable_and_tangent_ext hU P' Q').2 g g' hg hg' fun x hx => ?_
    obtain ⟨c, hc, -⟩ := hb.2 x hx
    have ec : c = ![c 0] := by
      ext i
      fin_cases i
      rfl
    rw [ec, LieMultiple.isLieComb_one_iff_comp] at hc
    rw [hc, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e₁
  have := P.isAb.smooth
  have := Q.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap s) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom s) s.injective
  exact ExtUnique.over_hom_ext_of_isPullback hP.2.1.1 (by rw [← eg, ← eg', e₂])

end GlobalTheory.HomUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorDet

section Algebra

noncomputable def rightAction (k O O' M : Type) [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M] : O' →+* Module.End k (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toRingHom.comp (Algebra.lsmul O O M : O' →ₐ[O] Module.End O M).toRingHom

variable {k O O' M : Type} [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem rightAction_apply (a : O') :
    rightAction k O O' M a = LinearMap.baseChange k (Algebra.lsmul O O M a : M →ₗ[O] M) := rfl

theorem rightAction_tmul (a : O') (c : k) (m : M) : rightAction k O O' M a (c ⊗ₜ m) = c ⊗ₜ (a • m) := rfl

theorem nonempty_eigenSub_equiv [Algebra O' k] [IsScalarTower O O' k] {I : Type} {σ : I → O' →+* k}
    (h : EigenSplit.IsSplitting σ) (i : I) (hi : σ i = algebraMap O' k) :
    Nonempty (EigenSplit.eigenSub (rightAction k O O' M) (σ i) ≃ₗ[k] k ⊗[O'] M) := by
  classical
  let ρ := rightAction k O O' M
  let π : k ⊗[O] M →ₗ[k] k ⊗[O'] M := ((TensorProduct.mk O' k M 1).restrictScalars O).liftBaseChange k
  have hπ : ∀ m, π (1 ⊗ₜ m) = 1 ⊗ₜ m := fun m => by simp [π]
  let ρ' : O' →+* Module.End k (k ⊗[O'] M) := (algebraMap k _).comp (σ i)
  have he : EigenSplit.IsEquivariant ρ ρ' π := fun a x => by
    have : π ∘ₗ ρ a = ρ' a ∘ₗ π := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, ρ, rightAction_tmul, hπ]
      simp [ρ', hi]
    exact congr($this x)
  let g : M →ₗ[O'] k ⊗[O] M :=
    { toFun := fun m => EigenSplit.proj h ρ i (1 ⊗ₜ m)
      map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a m => by
        rw [← rightAction_tmul, ← (EigenSplit.isEquivariant_action ρ a).proj h,
          EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ i _), hi, algebraMap_smul]
        rfl }
  let s : k ⊗[O'] M →ₗ[k] k ⊗[O] M := g.liftBaseChange k
  have h1 : s ∘ₗ π = EigenSplit.proj h ρ i := by
    ext m
    simp [hπ, s, g]
  have h2 : ∀ x, π (EigenSplit.proj h ρ i x) = π x := fun x => by
    rw [he.proj h]
    exact EigenSplit.proj_of_mem h (EigenSplit.mem_eigenSub.2 fun a => rfl)
  have h3 : π ∘ₗ s = LinearMap.id := by
    ext m
    simp [s, g, h2, hπ]
  refine ⟨LinearEquiv.ofBijective (π ∘ₗ Submodule.subtype _) ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun y => ⟨EigenSplit.projTo h ρ i (s y), (h2 _).trans congr($h3 y)⟩⟩⟩
  refine Subtype.ext ((EigenSplit.proj_of_mem h x.2).symm.trans ?_)
  rw [← h1]
  exact (congrArg s hx).trans (map_zero s)

end Algebra

theorem injective_of_charZero {E k : Type} [Field E] [NumberField E] [Field k] [CharZero k] (τ : 𝓞 E →+* k) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot, ← Ideal.absNorm_eq_zero_iff]
  simpa using RingHom.mem_ker.1 (Ideal.absNorm_mem (RingHom.ker τ))

theorem finrank_eigenSub {E k O M : Type} [Field E] [NumberField E] [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing O] [Algebra O k] [Algebra O (𝓞 E)] [AddCommGroup M] [Module O M] [Module (𝓞 E) M]
    [IsScalarTower O (𝓞 E) M] (τ : 𝓞 E →+* k) (hτ : τ.comp (algebraMap O (𝓞 E)) = algebraMap O k) :
    Module.finrank k (EigenSplit.eigenSub (rightAction k O (𝓞 E) M) τ) = Module.finrank (𝓞 E) M := by
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    classical
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have hi := injective_of_charZero τ
  let _ := τ.toAlgebra
  have : IsScalarTower O (𝓞 E) k := IsScalarTower.of_algebraMap_eq' hτ.symm
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have e : (IsFractionRing.lift hi : E →+* k).comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hi a
  obtain ⟨f⟩ := nonempty_eigenSub_equiv (O := O) (M := M) hs (IsFractionRing.lift hi) e
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq, ← f.finrank_eq, e]

theorem lieMult_of_param {k O V : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A : Over (Sp k)} [GrpObj A] (act : OAct O A) (ρ : O →+* Module.End k V) (Φ : V → (epsR k ⟶ A))
    (inj : Function.Injective Φ) (tan : ∀ x, IsTangent x ↔ x ∈ Set.range Φ) (add : ∀ y z, Φ (y + z) = Φ y * Φ z)
    (smul : ∀ (c : k) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) (eqv : ∀ a y, Φ (ρ a y) = Φ y ≫ act.act a)
    (τ : O →+* k) {n : ℕ} (hn : Module.finrank k (EigenSplit.eigenSub ρ τ) = n) :
    LieMult act (𝟙 (Sp k)) τ n := by
  have sm : ∀ (c : k) y x, x.left = spMap (epsScaleR c) ≫ (Φ y).left ↔ x = Φ (c • y) := fun c y x => by
    rw [← (LieMultiple.isLieComb_one_iff _ _ _).1 (smul c y)]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => by rw [h]⟩
  let F : Multiplicative V →* (epsR k ⟶ A) := MonoidHom.mk' (fun y => Φ y.toAdd) (fun y z => add _ _)
  have pr : ∀ (n : ℕ) (y : Fin n → V), (List.ofFn fun i => Φ (y i)).prod = Φ (∑ i, y i) := fun n y => by
    have := map_list_prod F (List.ofFn fun i => Multiplicative.ofAdd (y i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  let B := Module.finBasisOfFinrankEq k _ hn
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ A) ≃* (epsR k ⟶ A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left = η[A].left := Category.id_comp _
  have mem : ∀ y, y ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, (Φ y ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ (Φ y).left := fun y => by
    rw [EigenSplit.mem_eigenSub]
    exact forall_congr' fun a => by rw [sm, ← eqv, inj.eq_iff]
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, (w ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ w.left)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) n
    ⟨fun i => Φ (B i), fun i => ⟨(tan _).2 ⟨_, rfl⟩, (mem _).1 (B i).2⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  obtain ⟨y, rfl⟩ := (tan w).1 hw
  let y' : EigenSplit.eigenSub ρ τ := ⟨y, (mem y).2 hw'⟩
  refine (existsUnique_congr fun d => ?_).1 (existsUnique_eq' (a' := B.equivFun y'))
  have e₁ : B.equivFun y' = d ↔ y = ∑ i, d i • (B i : V) := by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [y']
  rw [e₁, ← inj.eq_iff, ← pr]
  constructor
  · exact fun h => ⟨_, fun i => (sm _ _ _).2 rfl, h⟩
  · rintro ⟨u, hu, h⟩
    rw [h, show u = fun i => Φ (d i • (B i : V)) from funext fun i => (sm _ _ _).1 (hu i)]

end GlobalTheory.TensorDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllipticCurveLatticeBaseChangeStable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem curve_lattice_baseChange : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  intro R _ P v Lf R₁ _ f P₁ φ v₁ ⟨hg, _, hfib, hlat⟩ hP₁ hv₁

  have up : ∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left)
      (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' →
      IsPolFibre (f'.comp f) P P' (φ' ≫ φ) ∧ IsVecOver (f'.comp f) (φ' ≫ φ) v v' := by
    intro R' _ f' P' φ' v' hP' hv'
    exact ⟨PolFibre.comp hP₁ hP', (PolFibre.vec_iff hP₁.2.1.1 hP'.2.1.1.w hv₁).1 hv'⟩
  refine ⟨hP₁.1.trans hg, hfib R₁ f P₁ φ v₁ hP₁ hv₁, ?_, ?_⟩
  · intro R' _ f' P' φ' v' hP' hv'
    obtain ⟨h₁, h₂⟩ := up R' f' P' φ' v' hP' hv'
    exact hfib R' (f'.comp f) P' (φ' ≫ φ) v' h₁ h₂
  · intro s' P' φ' v' u' w' hP' hv' hd
    obtain ⟨h₁, h₂⟩ := up ℂ s' P' φ' v' hP' hv'
    exact hlat (s'.comp f) P' (φ' ≫ φ) v' u' w' h₁ h₂ hd

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in

theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in

theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G'] in

theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

omit [GrpObj B] [GrpObj B'] in

theorem mul_over (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π) {φ₁ φ₂ : B ⟶ G} {φ₁' φ₂' : B' ⟶ G'}
    (h₁ : φ₁'.left ≫ π = β ≫ φ₁.left) (h₂ : φ₂'.left ≫ π = β ≫ φ₂.left) :
    (φ₁' * φ₂').left ≫ π = β ≫ (φ₁ * φ₂).left := by
  let U : Over.mk (B'.hom ≫ f) ⟶ B := Over.homMk β hβ
  rw [← hπ.2 B' _ _ (U ≫ φ₁) (U ≫ φ₂) h₁.symm h₂.symm, ← MonObj.comp_mul]
  rfl

end Grp

theorem lbIso_pow_over {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n n' : ℕ}
    (hI : LBIso (lbPow (P.pull φ) n) (lbPow M n')) : LBIso (lbPow (P'.pull φ') n) (lbPow M' n') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow (pull_isLB hP' _) _) (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _)
    (isLB_lbPow hM' _) (lbIso_lbPow e₃ n) ?_
  exact LBIso.trans (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow (pull_isLB hM _) _) (isLB_lbPow hM' _)
    (LBIso.chartPull (chartPullPowPull _ β _) (chartPullPowPull M β _) hI) (lbIso_lbPow eM.symm _)

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem IsHomFamily.baseChange {D : Datum H} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'}
    {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {B : Over (Sp R)} {B' : Over (Sp R')} [GrpObj B] [GrpObj B'] {β : B'.left ⟶ B.left}
    (hβ : IsGrpPullback B' B (spMap f) β) {M : LB B.left} {M' : LB B'.left} (hM : M.IsLB) (hM' : M'.IsLB)
    (eM : LBIso M' (M.pull β)) {v : epsR R ⟶ B} {v' : epsR R' ⟶ B'}
    (hv : v'.left ≫ β = spMap (Chart.dualMapR f) ≫ v.left) {L : Submodule (𝓞 E) D.La} {ρ : R} {S : Set L}
    {φ : L → (B ⟶ t.G)} {φ' : L → (B' ⟶ t'.G)} (hφ : ∀ a, (φ' a).left ≫ m.φ = β ≫ (φ a).left)
    (h : IsHomFamily t B M v L ρ S φ) : IsHomFamily t' B' M' v' L (f ρ) S φ' := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have hact : ∀ s a, (φ' a ≫ t'.act.act s).left ≫ m.φ = β ≫ (φ a ≫ t.act.act s).left := fun s a => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc]
  refine ⟨fun a => have := h₁ a; isMonHom_over hβ m.cart (hφ a), fun a b => eq_of_comp_eq m.cart.1 ?_,
    fun s a => eq_of_comp_eq m.cart.1 ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [mul_over hβ.1.w m.cart (hφ a) (hφ b), ← h₂]
    exact hφ _
  · rw [hact, ← h₃]
    exact hφ _
  · have e := (LieMultiple.isLieComb_one_iff _ _ _).1 (h₄ a)
    rw [LieMultiple.isLieComb_one_iff_comp]
    refine eq_of_comp_eq m.cart.1 ?_
    show (v'.left ≫ (φ' a ≫ t'.act.act H.rt).left) ≫ m.φ = (spMap (epsScaleR (f ρ)) ≫ v'.left ≫ (φ' a).left) ≫ m.φ
    rw [Category.assoc, hact, Category.assoc, Category.assoc, hφ, ← Category.assoc, ← Category.assoc v'.left, hv,
      Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
      spMap_spMap, spMap_spMap]
    congr 2
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨N, hN, hI⟩ := h₅ a ha
    obtain ⟨w, g, -⟩ := m.lin
    exact ⟨N, hN, lbIso_pow_over (hφ a) t.PP.isLB t'.PP.isLB hM hM' ⟨w, g⟩ eM hI⟩

end PureType

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.exists_weierstrass_coordinates_on_line : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  first | exact @GlobalTheory.UnifCoord.exists_coord_on_line | exact GlobalTheory.UnifCoord.exists_coord_on_line | (intros; apply GlobalTheory.UnifCoord.exists_coord_on_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformisationTangentUnimodularRiemanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.AnyUnif.tangent_and_unimodular | exact GlobalTheory.AnyUnif.tangent_and_unimodular | (intros; apply GlobalTheory.AnyUnif.tangent_and_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
theorem _root_.GlobalTheory.T.tensor_map_finite_of_split : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) [IsCommMonObj P.A] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O P.A) (b : OAct O A) (t : IsTensor A b P.A a M) (n k : ℕ) (l : M →ₗ[O] (Fin k → O)) (r : (Fin k → O) →ₗ[O] M), 0 < n → (∀ m, r (l m) = n • m) → IsFinite (t.mapLeft (IsTensor.pow (Out.powIsPowGrp P.A k) a) l).left := by
  first | exact @GlobalTheory.TensorFinite.isFinite_mapLeft | exact GlobalTheory.TensorFinite.isFinite_mapLeft | (intros; apply GlobalTheory.TensorFinite.isFinite_mapLeft <;> assumption)
end

