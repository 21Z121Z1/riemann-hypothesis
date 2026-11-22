import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorQuasiLogarithmOfCongruentCombinatio
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.TangentComb

theorem in_top_add_smul {O Q σ : Type} [CommRing O] [CommRing Q] [Algebra O Q]
    {f g : MvPowerSeries σ Q} (hf : In (⊤ : Ideal O) f) (hg : In (⊤ : Ideal O) g) (a : O) :
    In (⊤ : Ideal O) (f + algebraMap O Q a • g) := by
  intro α
  obtain ⟨b, -, hb⟩ := hf α
  obtain ⟨b', -, hb'⟩ := hg α
  refine ⟨b + a * b', trivial, ?_⟩
  rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]

theorem ql_add_smul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) :
    QL μ ⊤ (f + algebraMap O Q a • g) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    obtain ⟨b', -, hb'⟩ := hg.2.1 i
    refine ⟨b + a * b', trivial, ?_⟩
    simp only [lin] at hb hb' ⊢
    rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]
  · rw [formalCoboundary_add hμ', formalCoboundary_smul hμ']
    exact in_top_add_smul hf.2.2 hg.2.2 a

theorem ql_zero {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) :
    QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  have h0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμ' (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    rwa [zero_smul, zero_smul] at this
  refine ⟨map_zero _, fun i => ⟨0, trivial, ?_⟩, ?_⟩
  · simp [lin]
  · rw [h0]
    exact In.top_iff.2 ⟨0, map_zero _⟩

end GlobalTheory.TangentComb

open GlobalTheory.TangentComb in
theorem GlobalTheory.TangentComb.main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c ι _ e he L hL g hg a hint
  classical
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have lin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF
  have hμ := c.isLaw.const

  have key : ∀ s : Finset ι, QL c.μ ⊤ (∑ m ∈ s, algebraMap O C (a m) • e m) ∧
      c.IsLie (∑ m ∈ s, algebraMap O C (a m) • e m) (∑ m ∈ s, a m • L m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨ql_zero hμ, c.isLie_zero hF.inj⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, add_comm, add_comm (a j • L j)]
      exact ⟨ql_add_smul hμ ih.1 (he j) (a j),
        (lin _ _ _ _ (a j) ih.2 (hL j)).1 ih.1 (he j)⟩
  obtain ⟨hQ, hI⟩ := key Finset.univ
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF g hg
  have h1 := (lin g (comb a e) l (∑ m, a m • L m) (-1) hl hI).1 hg hQ
  have hser : g + algebraMap O C (-1) • comb a e = g - comb a e := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [hser] at h1
  obtain ⟨s, hs⟩ := In.top_iff.1 hint
  have h0 := (lin _ (comb a e) _ (∑ m, a m • L m) 0 h1 hI).2.1 ⟨s, hs.symm⟩
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0 ▸ hl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorAlgebraProductDiagramCompat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.KunnethOne

theorem tensor_eq_zero_of_forall {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V ⊗[K] W)
    (h : ∀ l : W →ₗ[K] K, TensorProduct.rid K V (LinearMap.lTensor V l t) = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K W
  have key : ∀ (j : Module.Free.ChooseBasisIndex K W) (s : V ⊗[K] W),
      TensorProduct.equivFinsuppOfBasisRight b s j =
        TensorProduct.rid K V (LinearMap.lTensor V (b.coord j) s) := by
    intro j s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  rw [key, h, map_zero, Finsupp.zero_apply]

section Contr

variable {K : Type} [Field K] {Q : Type} [Category.{0} Q] (G : Q ⥤ CommAlgCat.{0} K)
  [Fintype Q] [DecidableEq Q] [∀ T T' : Q, Fintype (T ⟶ T')] [∀ T T' : Q, DecidableEq (T ⟶ T')]

def coef (Λ : C1 G →ₗ[K] K) (T T' : Q) (φ : T ⟶ T') : G.obj T' →ₗ[K] K :=
  Λ ∘ₗ LinearMap.single K (fun T => ∀ (T' : Q) (_ : T ⟶ T'), G.obj T') T ∘ₗ
    LinearMap.single K (fun T' => (T ⟶ T') → G.obj T') T' ∘ₗ
    LinearMap.single K (fun _ : T ⟶ T' => G.obj T') φ

def contr (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) :
    (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') →ₗ[K] M :=
  ∑ T, ∑ T', ∑ φ : T ⟶ T', (TensorProduct.rid K M).toLinearMap ∘ₗ
    LinearMap.lTensor M (coef G Λ T T' φ) ∘ₗ
    LinearMap.proj (R := K) (φ := fun _ : T ⟶ T' => M ⊗[K] G.obj T') φ ∘ₗ
    LinearMap.proj (R := K) (φ := fun T' => (T ⟶ T') → M ⊗[K] G.obj T') T' ∘ₗ
    LinearMap.proj (R := K) (φ := fun T => ∀ (T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') T

theorem contr_apply (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G M Λ c = ∑ T, ∑ T', ∑ φ : T ⟶ T',
      TensorProduct.rid K M (LinearMap.lTensor M (coef G Λ T T' φ) (c T T' φ)) := by
  simp [contr, LinearMap.sum_apply]

theorem contr_tmul (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) (z : M)
    (h : C1 G) : contr G M Λ (fun T T' φ => z ⊗ₜ[K] h T T' φ) = Λ h • z := by
  rw [contr_apply]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, ← Finset.sum_smul]
  congr 1
  simp only [coef, LinearMap.comp_apply, ← map_sum]
  congr 1
  simp only [LinearMap.single_apply, Finset.univ_sum_single]

theorem contr_natural (M N : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Λ : C1 G →ₗ[K] K) (h : M →ₗ[K] N) (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G N Λ (fun T T' φ => LinearMap.rTensor (G.obj T') h (c T T' φ)) = h (contr G M Λ c) := by
  simp only [contr_apply, map_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ =>
    Finset.sum_congr rfl fun φ _ => ?_
  induction c T T' φ using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem kunneth_contraction_d0_vanishes (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (hΛ : ∀ g : C0 G, Λ (d0 G g) = 0) (w : ∀ T : Q, M ⊗[K] G.obj T) :
    contr G M Λ (fun T T' φ => LinearMap.lTensor M (mp G φ).toLinearMap (w T) - w T') = 0 := by
  let D : (∀ T : Q, M ⊗[K] G.obj T) →ₗ[K] (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :=
    LinearMap.pi fun T => LinearMap.pi fun T' => LinearMap.pi fun φ =>
      LinearMap.lTensor M (mp G φ).toLinearMap ∘ₗ
        LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T -
      LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T'
  have hD : contr G M Λ ∘ₗ D = 0 := by
    refine LinearMap.pi_ext fun T₀ x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      have e : D (Pi.single T₀ (z ⊗ₜ[K] u)) =
          fun T T' φ => z ⊗ₜ[K] (-d0 G (Pi.single T₀ u : C0 G) T T' φ) := by
        funext T T' φ
        simp only [D, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, amitsur_d0_apply, neg_sub, TensorProduct.tmul_sub]
        by_cases h1 : T = T₀ <;> by_cases h2 : T' = T₀
        · subst h1; subst h2; simp
        · subst h1; simp [Pi.single_eq_of_ne h2]
        · subst h2; simp [Pi.single_eq_of_ne h1]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have c := contr_tmul G M Λ z (-d0 G (Pi.single T₀ u : C0 G))
      simp only [Pi.neg_apply] at c
      rw [LinearMap.comp_apply, e, c, map_neg, hΛ, neg_zero, zero_smul, LinearMap.zero_apply]
    | add u v hu hv => simp only [Pi.single_add, map_add, hu, hv]
  exact LinearMap.congr_fun hD w

end Contr

end GlobalTheory.CatCoh.KunnethOne

namespace GlobalTheory.CatCoh.KunnethOne

theorem sum_tmul_eq_zero_of_cup : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  intro K _ P Q _ _ _ _ F G E i₁ i₂ h₁ h₂ hb n x y f hf
  classical
  haveI := Fintype.ofFinite Q
  haveI : ∀ T T' : Q, Fintype (T ⟶ T') := fun _ _ => Fintype.ofFinite _
  apply tensor_eq_zero_of_forall
  intro l
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l ∘ₗ H1.mk G)
  have hΛy : ∀ z : Z1 G, Λ z.1 = l (H1.mk G z) := fun z => LinearMap.congr_fun hΛ z
  have hΛd : ∀ g : C0 G, Λ (d0 G g) = 0 := fun g => by
    have e := hΛy ⟨d0 G g, commAlgFunctorCoboundaryZero_mem_cocyclesOne G g⟩
    rw [e, H1.mk_eq_zero.2 ⟨g, rfl⟩, map_zero]
  simp only [← hΛy, ← map_smul, ← map_sum]
  rw [H1.mk_eq_zero]
  let β : ∀ T : P × Q, F.obj T.1 ⊗[K] G.obj T.2 ≃ₐ[K] E.obj T :=
    fun T => AlgEquiv.ofBijective _ (hb T)
  have hβ : ∀ (T : P × Q) (z : F.obj T.1) (u : G.obj T.2), β T (z ⊗ₜ u) = i₁ T z * i₂ T u :=
    fun T z u => Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have natL : ∀ (p p' : P) (T : Q) (a : p ⟶ p') (t : F.obj p ⊗[K] G.obj T),
      β (p', T) (LinearMap.rTensor (G.obj T) (mp F a).toLinearMap t) =
        mp E ((a, 𝟙 T) : (p, T) ⟶ (p', T)) (β (p, T) t) := by
    intro p p' T a t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.rTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p', T), ← h₂ (p, T) (p', T)]
      simp [mp_id]
    | add u v hu hv => simp only [map_add, hu, hv]
  have natR : ∀ (p : P) (T T' : Q) (b : T ⟶ T') (t : F.obj p ⊗[K] G.obj T),
      β (p, T') (LinearMap.lTensor (F.obj p) (mp G b).toLinearMap t) =
        mp E ((𝟙 p, b) : (p, T) ⟶ (p, T')) (β (p, T) t) := by
    intro p T T' b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.lTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p, T'), ← h₂ (p, T) (p, T')]
      simp [mp_id]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨fun p => contr G (F.obj p) Λ
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T')))), ?_⟩
  funext p p' a
  rw [amitsur_d0_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have step : ∀ (T T' : Q) (b : T ⟶ T'),
      (β (p', T')).symm (f (p', T) (p', T') ((𝟙 p', b) : (p', T) ⟶ (p', T'))) -
        LinearMap.rTensor (G.obj T') (mp F a).toLinearMap
          ((β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, b) : (p, T) ⟶ (p, T')))) =
      ∑ i, (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' b -
        (LinearMap.lTensor (F.obj p') (mp G b).toLinearMap
            ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
          (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T')))) := by
    intro T T' b
    apply (β (p', T')).injective
    have H1 := hf (p, T) (p', T) (p', T') (a, 𝟙 T) (𝟙 p', b)
    have H2 := hf (p, T) (p, T') (p', T') (𝟙 p, b) (a, 𝟙 T')
    rw [d1_apply] at H1 H2
    simp only [prod_comp, Category.comp_id, Category.id_comp] at H1 H2
    simp only [Z1.id, map_zero, zero_mul, Finset.sum_const_zero] at H2
    simp only [← h₁, mp_id] at H1
    simp only [map_sub, map_sum, AlgEquiv.apply_symm_apply, natL, natR, hβ]
    linear_combination H1 - H2
  have nat := contr_natural G (F.obj p) (F.obj p') Λ (mp F a).toLinearMap
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T'))))
  rw [AlgHom.toLinearMap_apply] at nat
  rw [← nat, ← map_sub]
  trans contr G (F.obj p') Λ ((∑ i, fun T T' φ => (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' φ) -
    fun T T' φ => LinearMap.lTensor (F.obj p') (mp G φ).toLinearMap
        ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
      (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T'))))
  · congr 1
    funext T T' b
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact step T T' b
  · rw [map_sub, kunneth_contraction_d0_vanishes _ _ _ hΛd, sub_zero, map_sum]
    simp only [contr_tmul]

end GlobalTheory.CatCoh.KunnethOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormDichotomy

theorem unit_or_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  intro F E _ _ _ _ _ σ h K _ _

  obtain ⟨e, he⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set d : E := e - σ e with hd
  have hσd : σ d = -d := by
    rw [hd, map_sub, GlobalTheory.HermLineZeros.conj_invol h]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply he; rw [hd, sub_eq_zero] at h0; exact h0.symm
  have hfix : σ (d * d) = d * d := by rw [map_mul, hσd]; ring
  obtain ⟨c0, hc0⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h _ hfix
  haveI : CharZero F := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set L := K ⊗[F] E
  set ι := algebraMap K L with hι
  set D : L := inclR K d with hD
  set c : K := algebraMap F K c0 with hc
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; apply hd0; rw [map_zero] at hc0; exact mul_self_eq_zero.1 hc0.symm
  have hcne : c ≠ 0 := by rw [hc]; exact (map_ne_zero _).2 hc0ne
  have hDD : D * D = ι c := by
    rw [hD, ← map_mul, ← hc0, hc, hι, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes c0
  have hsD : sigR K σ D = -D := by
    show inclR K (σ d) = _
    rw [hσd, map_neg]
  have hst : ∀ t : K, sigR K σ (ι t) = ι t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl

  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst0
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst0
    have e2 := congrArg σ hst0
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσd, map_zero] at e2
    have ht : algebraMap F E t * d = 0 := by linear_combination (hst0 - e2) / 2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h1 | h1
      · exact (map_eq_zero _).1 h1
      · exact absurd h1 hd0
    refine ⟨?_, ht0⟩
    rw [ht0, map_zero, zero_mul, add_zero] at hst0
    exact (map_eq_zero _).1 hst0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bK := Algebra.TensorProduct.basis K b
  have hdec : ∀ a : L, ∃ u v : K, a = ι u + ι v * D := by
    intro a
    refine ⟨bK.repr a 0, bK.repr a 1, ?_⟩
    conv_lhs => rw [← bK.sum_repr a]
    rw [Fin.sum_univ_two]
    have hb : ⇑b = ![(1 : E), d] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h0 : bK 0 = 1 := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_zero]; rfl
    have h1 : bK 1 = D := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_one, Matrix.head_cons]; rfl
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  by_cases hsq : ∃ r : K, r * r = c
  · right
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hcne (by rw [← hr, mul_zero])
    have h2 : ι (1 / 2) * 2 = 1 := by
      rw [show (2 : L) = ι 2 from (map_ofNat ι 2).symm, ← map_mul]; norm_num
    have hs : ι r * ι r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
    have hD2 : D * D = ι r * ι r := by rw [hDD, ← hr, map_mul]
    set ε : L := ι (1 / 2) * (1 + ι r⁻¹ * D) with hε
    have he0 : ε * (1 - ε) = 0 := by
      rw [hε]
      linear_combination (-(1 + ι r⁻¹ * D) * ι (1 / 2)) * h2 + (-ι (1 / 2) ^ 2 * ι r⁻¹ ^ 2) * hD2 + (-ι (1 / 2) ^ 2 * (ι r⁻¹ * ι r + 1)) * hs
    have hσε : sigR K σ ε = 1 - ε := by
      rw [hε, map_mul, map_add, map_mul, map_one, hst, hst, hsD]
      linear_combination h2
    intro k _
    refine ⟨ι k * ε + (1 - ε), ?_⟩
    rw [map_add, map_mul, map_sub, map_one, hst, hσε]
    linear_combination (ι k ^ 2 + 1 - 2 * ι k) * he0
  · left
    push_neg at hsq
    intro a ha
    obtain ⟨u, v, rfl⟩ := hdec a
    have hn : u * u - c * (v * v) ≠ 0 := by
      intro h0
      by_cases hv : v = 0
      · apply ha
        have : u * u = 0 := by rw [hv] at h0; simpa using h0
        rw [mul_self_eq_zero.1 this, hv, map_zero, zero_mul, add_zero]
      · apply hsq (u / v)
        field_simp
        linear_combination h0
    have hN : (ι u + ι v * D) * sigR K σ (ι u + ι v * D) = ι (u * u - c * (v * v)) := by
      rw [map_add, map_mul, hst, hst, hsD, map_sub, map_mul, map_mul, map_mul]
      linear_combination (-(ι v * ι v)) * hDD
    refine IsUnit.of_mul_eq_one (sigR K σ (ι u + ι v * D) * ι (u * u - c * (v * v))⁻¹) ?_
    rw [← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hn, map_one]

end GlobalTheory.NormDichotomy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelations
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open RingTheory.Sequence in

theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatricesStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.window_lift_to_fontaineAinf_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  first | exact @GlobalTheory.WinLift.Top.window_lift | exact GlobalTheory.WinLift.Top.window_lift | (intros; apply GlobalTheory.WinLift.Top.window_lift <;> assumption)
end

