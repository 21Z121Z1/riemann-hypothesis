import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddClosure

theorem addB_of_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (s s' : Fin n → Raw D F 2)
    (h₀ : PullB D F (toUnit _) 1 f₀ s₀) (h : ∀ i, PullB D F (toUnit _) 2 (f i) (s i))
    (h' : ∀ i, PullB D F (toUnit _) 2 (f' i) (s' i)) (hB : AddB D (𝟙_ _) f₀ r f f') :
    AddB D (TF (R := R) F) s₀ r s s' := by
  intro T ρ x y z J hJ
  obtain ⟨h1, h2⟩ := hB T (ρ ≫ toUnit _) x y z J hJ
  have e₀ := fun α w => GlobalTheory.pullB_values R D F _ _ 1 f₀ s₀ h₀ α T ρ w z J hJ
  have e := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f i) (s i) (h i) α T ρ w z J hJ
  have e' := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f' i) (s' i) (h' i) α T ρ w z J hJ
  refine ⟨fun a b α β ha hb => ?_, fun α β hn => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((h1 a b α β ha hb).trans ?_)
    · exact congrArg₂ (· * ·) (e i α x) (e' i β y)
    · exact congrArg _ (congrArg₂ (· * ·) (e₀ a _).symm (e₀ b _).symm)
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h2 α β hn)
    exact congrArg₂ (· * ·) (e i α x) (e' i β y)

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hth hs₀
  obtain ⟨r, n, σ, σ', hr, hG⟩ := GlobalTheory.T.exists_integral_addition_formula_group V hV D A G U θ
  have hexp := GlobalTheory.BaseExpansionExists.main hL hL2 V hV D A G U 2 (by norm_num)
  choose g hg using hexp
  obtain ⟨hpG, hpB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 2
  choose pt hpt using fun σ => (hpG σ).exists
  choose ps hps using fun f => (hpB f).exists
  have hB := GlobalTheory.T.additionFormula_coefficients_abelian_square hL.globalFns V hV D A G U θ f r n σ σ' (fun i => g (σ i)) (fun i => g (σ' i)) hG hθ.1
    (fun i => ⟨hg _, hg _⟩)
  refine ⟨r, n, fun i => pt (σ i), fun i => pt (σ' i), fun i => ps (g (σ i)), fun i => ps (g (σ' i)), hr,
    fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.AddGeneric.addA_of_addG V D _ A G U (Kbar V) θ r n σ σ' th _ _ hr hG hth (fun i => ⟨hpt _, hpt _⟩)
  · exact addB_of_pull D (Kbar V) f s₀ r _ _ _ _ hs₀ (fun i => hps _) (fun i => hps _) hB

end GlobalTheory.AddClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupport
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddTensor

theorem full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  intro h1 h2 S _ P F _ _ p h2F th n t t' hadd hth
  choose Φ hΦ hΦu _ using GlobalTheory.ThetaLin.main S P F p 2
  refine GlobalTheory.eigenTensor_full_left_support F (EA P p 2) (EA P p 2)
    {θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p) // θ.pt ^ 2 = 1}
    (fun θ => (Φ θ.1 : EA P p 2 →ₗ[F] EA P p 2)) (fun θ => Φ θ.1) ?_ _
    (GlobalTheory.T.additionFormula_tensor_ne_zero S P F p th n t t' hadd hth) ?_
  · intro U hU
    refine (GlobalTheory.T.abelian_sections_irreducible_theta_group h1 h2 S P F p 2 (by exact_mod_cast h2F)).2 U ?_
    intro θ hθ v v' hvv' hv
    have e : v' = Φ θ v := hΦu θ v.sec v'.sec hvv'
    rw [e]
    exact hU ⟨θ, hθ⟩ v hv
  · intro θ
    obtain ⟨r, hr⟩ := GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two h1.globalFns S P F p th n t t' (fun i => Φ θ.1 (t i)) (fun i => Φ θ.1 (t' i))
      hadd θ.1 θ.2 (fun i => ⟨hΦ θ.1 (t i), hΦ θ.1 (t' i)⟩)
    refine ⟨r, Eq.trans ?_ hr⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.map_tmul _ _ _ _

end GlobalTheory.AddTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EvalLevel
open GlobalTheory.UT.CoefBasic

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem powFrame_isGen (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_translPt (x : T ⟶ A) : ptSecT A (1 : T ⟶ A) ≫ translPt A x = x := by
  rw [ptSecT, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, ← Hom.mul_def, _root_.mul_one]

theorem ptSec_translT (x : T ⟶ A) : (ptSecT A (1 : T ⟶ A)).left ≫ (translT A x).left = (ptSecT A x).left := by
  rw [← Over.comp_left, translT, comp_lift, ptSec_translPt, ptSecT, lift_fst]; rfl

end

theorem sumV_mul {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s c : F}
    (h : SumV v x s) (hc : c ≠ 0) : SumV v (fun i => c * x i) (c * s) := by
  intro q
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨S, hS⟩ := h (q - r)
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub, v.map_mul, ← hr, show q = r + (q - r) by ring, WithTop.coe_add]
  exact add_le_add le_rfl (hS T hT)

theorem sumV_equiv {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix Ix' : Type} (e : Ix' ≃ Ix) {x : Ix → F} {s : F}
    (h : SumV v x s) : SumV v (fun i => x (e i)) s := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) fun i hi => by
    simpa using hT (Finset.mem_map_of_mem e.symm.toEmbedding hi)
  rwa [Finset.sum_map] at this

theorem exists_act_value {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) (N : ℕ)
    (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F))
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => θ.pt.left) (fun _ => 1)))
    (he : e.IsGen) : ∃ u : F, u ≠ 0 ∧ ∀ (t t' : SecA A F N) (c : F), IsActOf A.A A.L (N : ℤ) θ t t' →
      (∀ z J, Good A.L z J → sA t (ptSecT A.A θ.pt).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z c) * (val (powFrame A.A A.L θ.pt e N) (𝟙 _) z J).val) →
      ∀ z J, Good A.L z J → sA t' (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z (u * c)) * (val (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (𝟙 _) z J).val := by
  have e₀ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  have e₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (translPt A.A θ.pt).left = θ.pt.left := by
    rw [← Over.comp_left, ptSec_translPt]
  obtain ⟨u, hu, hv⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ θ.φ (ptSecT A.A 1).left) (powFrame A.A A.L θ.pt e N))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) (powFrame_isGen θ.pt e he N))
    (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (rigT_isGen hρ N) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      exact (congrArg₂ (fun a b => h a ^ (N : ℤ) * (h b ^ (N : ℤ))⁻¹ * h θ.pt.left ^ (N : ℤ)) e₀ e₁).trans
        (inv_mul_cancel_right _ _))
  refine ⟨u, hu, fun t t' c ha ht z J hJ => ?_⟩
  have a₁ := GlobalTheory.BoxTheta.act_val θ t t' ha (ptSecT A.A 1).left z hJ
  rw [ptSec_translT] at a₁
  have a₀ := (val_pull (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (ε := ![(N : ℤ), -(N : ℤ)]) hJ θ.φ (ptSecT A.A 1).left (𝟙 _)).trans
    (congrArg (fun r => val (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
      (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ r z J) (Category.id_comp _))
  have a₂ := ((Units.val_mul _ _).symm.trans (congrArg Units.val ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₀ rfl)).symm)).trans (hv _ (𝟙 _) z J hJ)
  have a₃ := ht z J hJ
  have a₄ : cst (R := R) F z (u * c) = cst (R := R) F z u * cst (R := R) F z c := by
    rw [cst_eq, cst_eq, cst_eq, map_mul]
  refine a₁.trans ((congrArg _ a₃).trans ?_)
  rw [a₄]
  refine (mul_left_comm _ _ _).trans ((congrArg _ a₂).trans ?_)
  exact (_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (fun a b : (TFK (R := R) F).left.presheaf.stalk z => a * b) (_root_.mul_comm _ _) rfl)

theorem value_at_level : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (N : ℕ), 1 ≤ N → ∀ (q : QkPt D.toPre F N) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F N q x → ∀ e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), e.IsGen → ∀ w : Frm D.toPre F N q.g.b, w.IsGen → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e N) (𝟙 _) z J).val) → SumV v (coef s q.g w) (κ * c) := by
  intro hL V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN N hN1 q x hx e he w hw
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  haveI : Subsingleton (TFK (R := V) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := V) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := V) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre F) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL V _ hB D F N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic V D.toPre F N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 F N hN1 w₀ hN.1).1 t'
  have h₁ := (GlobalTheory.UT.EvalZero.value_at_origin hL V _ hB D A G hG U F).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := sumV_equiv (Equiv.addRight q.y) (GlobalTheory.UT.AdicValSum.main V ϖ hϖ F v hv _ _ _ h₁).1
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumV_mul h₂ hd
  simp only [Equiv.coe_addRight, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

end GlobalTheory.UT.EvalLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

theorem toBase_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (hw : F ≫ G.hom = G'.hom ≫ f) (T : Over S') (x y : T ⟶ G') :
    toBase hw (x * y) = toBase hw x * toBase hw y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) (e : f = f') (e' : F = F') (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left}
    {hw w hw'' w''} (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' := by
  subst e e'
  exact ((isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF.1.w _ h).2 (toBase_mul hF _) _ h'').imp fun _ => And.left

theorem exists_even_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    [IsMonHom i'] (hi : TorusCompat f F i' i) (σ : CubTriv P.c i) (hσ : σ.Even) :
    ∃ σ' : CubTriv P'.c i', σ'.Even := by
  have hE := SplitTorus.isGrpPullback_bcMap f X
  rw [torusCompat_iff] at hi
  have hc : ∀ k : Fin 2, ![i'.left, (1 : splitTorus S' X ⟶ G').left] k ≫ F =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus S X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · show (1 : splitTorus S' X ⟶ G').left ≫ F = SplitTorus.bcMap f X ≫ (1 : splitTorus S X ⟶ G).left
      rw [one_left_comp h.mul, one_left, ← Category.assoc, hE.1.w]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 h.gen) P.L.isLB P'.L.isLB _ hc σ.s σ.gen
  let β := toBaseHom (toBase_mul hE hE.1.w)
  have hβ : ∀ {T : Over S'} (t : T ⟶ splitTorus S' X), β T t ≫ i = toBase hw (t ≫ i') := fun t =>
    Over.OverMorphism.ext (by
      show (t.left ≫ SplitTorus.bcMap f X) ≫ i.left = (t.left ≫ i'.left) ≫ F
      rw [Category.assoc, hi, Category.assoc])
  have vs : ∀ (T : Over S') (z : T.left) (J') (J), Good P'.L.L z J' → Good P.L.L z J →
      ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      ∀ t : T ⟶ splitTorus S' X, @id (T.left.presheaf.stalk z)ˣ (val σ.s (β T t).left z J) =
        W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := by
    intro T z J' J hJ' hJ W hW t
    refine (CubTransport.val_pmaps hc Hs t.left hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    rw [hW, hW]
    exact CubTrivTorus.prod_cubTriv i' t (fun q => gw w q z (J (q ≫ F)) (J' q))
  refine ⟨⟨s, hs, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.2 (x ≫ i') (y ≫ i') (u ≫ i')
    obtain ⟨Z, hZ⟩ : ∃ Z : (T ⟶ splitTorus S' X) → (T.left.presheaf.stalk z)ˣ,
      ∀ t, Z t = val σ.s (β T t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β T x) (β T y) (β T u) z J hJ
    simp only [← map_mul, hβ] at b
    have b' : Z (x * y * u) * Z x * Z y * Z u = @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) *
        Z (x * y) * Z (x * u) * Z (y * u) := by
      simp only [hZ]; exact b
    have v : ∀ t, Z t = W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := fun t => (hZ t).trans (vs T z J' J hJ' hJ W hW t)
    generalize @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) = C
      at a b'
    simp only [v, MonObj.mul_comp] at b'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i')
    have b := hσ _ (β T x) z J hJ
    rw [← map_inv, hβ] at b
    have b' : W (x⁻¹ ≫ i') * (W 1)⁻¹ * val s (x⁻¹).left z J' =
        val P.sym ((x ≫ i').left ≫ F) z J * (W (x ≫ i') * (W 1)⁻¹ * val s x.left z J') := by
      rw [← vs T z J' J hJ' hJ W hW, ← vs T z J' J hJ' hJ W hW]; exact b
    rw [GrpObj.inv_comp] at b'
    show val s _ z J' = _ * val s _ z J'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''

theorem nonempty_biTriv (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (i : splitTorus _ X ⟶ G)
    (hi : IsMonHom i) : Nonempty (BiTriv P.c i) := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let f := red (IsLocalRing.maximalIdeal A)
  have hF := isGrpPullback_pullback G f
  have : Smooth ((Over.pullback f).obj G).hom := by show Smooth (pullback.snd G.hom f); infer_instance
  have : GeometricallyConnected ((Over.pullback f).obj G).hom := by
    show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ ((Over.pullback f).obj G)).1
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback f).obj G) hF.1 i
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := exists_isCPMap P (toBase_mul hF hF.1.w) _ (pull_isLB P.L.isLB _) _
    (pullIso_isGen P.L.isLB _)
  exact T.nonempty_biTriv_of_nonempty_biTriv_reduction A _ hA X G _ _ _ hF P _ _ hP i i₀ hi (h₀.isMonHom hF) h₀
    (BiextTriv.main _ X _ _ _ i₀ (h₀.isMonHom hF))

theorem nonempty_desc (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (Q : TQ G X)
    (h : ∃ σ : CubTriv P.c Q.i, σ.Even) : Nonempty (Q.Desc P) := by
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ G).1
  exact UU.nonempty_desc _ X G Q P (nonempty_biTriv A hA G P Q.i Q.i_hom) h

theorem exists_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w) (Q' : TQ G' X)
    (h : ∃ σ : CubTriv P'.c Q'.i, σ.Even) :
    ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i ∧ ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨Q₀, h₀⟩ := exists_tq_baseChange _ _ g X G' _ _ hG Q'
  obtain ⟨Q, hQ⟩ := TorusQuotLift.main A _ hN X G _ _ hF₀ Q₀
  refine ⟨Q, ?_, ?_⟩
  · have : IsIso (SplitTorus.bcMap g X) := (SplitTorus.isGrpPullback_bcMap g X).1.isIso_fst_of_isIso
    rw [torusCompat_iff] at h₀ hQ ⊢
    rw [← cancel_epi (SplitTorus.bcMap g X), ← Category.assoc, ← bcMap_comp, hg, hQ, ← Category.assoc, ← h₀,
      Category.assoc]
  · obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
      (pullIso_isGen P'.L.isLB _)
    obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
    obtain ⟨_, h₂⟩ := exists_congr h₁ hg rfl hF₀.1.w
    obtain ⟨σ, hσ⟩ := h
    have := Q₀.i_hom
    exact T.exists_even_cubicalTrivialisation_lift_nilpotent A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ Q.i Q₀.i Q.i_hom Q₀.i_hom hQ
      (nonempty_biTriv A hA G P Q.i Q.i_hom) (exists_even_pull hP₀ h₀ σ hσ)

theorem exists_transition {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {P : CP G} {P' : CP G'} {hw} {w}
    (hP : IsCPMap P' P f F hw w) {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P)
    (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨β, hq, hβ⟩ := TQ.exists_isGrpPullback _ _ f X G G' F hF Q Q' h
  obtain ⟨_, -, h₁⟩ := D.map.exists_comp hP (by rw [Category.assoc, Over.w, Category.comp_id, hw])
  obtain ⟨_, h₂⟩ := exists_congr h₁ (Category.comp_id f) hq.symm (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w])
  exact ⟨β, ⟨hβ, isCPMap_descends _ _ f X G' Q' P' D' Q.B D.M β hβ.1.w _ _ (toBase_mul hβ _) h₂⟩, hq⟩

end GlobalTheory.UU.TowerEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expansion_section_lineBundle_power : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  first | exact @GlobalTheory.BaseExpansionExists.main | exact GlobalTheory.BaseExpansionExists.main | (intros; apply GlobalTheory.BaseExpansionExists.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyFunctionalEquation_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  first | exact @GlobalTheory.famFE_field_change | exact GlobalTheory.famFE_field_change | (intros; apply GlobalTheory.famFE_field_change <;> assumption)
end

