import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImInvIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DerivationEqZeroOfKodairaSpencerZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_eq_zero_of_kodairaSpencer_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  first | exact @GlobalTheory.KS.KerZero.derivation_eq_zero_of_ks_zero | exact GlobalTheory.KS.KerZero.derivation_eq_zero_of_ks_zero | (intros; apply GlobalTheory.KS.KerZero.derivation_eq_zero_of_ks_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromC_sharpClass_fibre_of_charZero : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (c : SiegPre h (N' ^ 2) (b.ζ : o) s), c.Principal → IsSharp W a bas t c → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (SharpClass (b := b) W a bas em) t x := by
  first | exact @GlobalTheory.SharpFrom.fromC_sharpClass | exact GlobalTheory.SharpFrom.fromC_sharpClass | (intros; apply GlobalTheory.SharpFrom.fromC_sharpClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace SharpObj

theorem omegaStd_sum_smul {h : ℕ} {I : Type} [Fintype I] (x : Fin h ⊕ Fin h → ℤ) (c : I → ℤ)
    (y : I → Fin h ⊕ Fin h → ℤ) : omegaStd x (∑ v, c v • y v) = ∑ v, c v * omegaStd x (y v) := by
  simp only [omegaStd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_act {h : ℕ} (G A : Matrix (Fin 8) (Fin 8) ℤ) (x : Fin 8 → Fin h ⊕ Fin h → ℤ) :
    ∑ u, ∑ v, G u v * omegaStd (x u) (∑ v', A v v' • x v') = ∑ u, ∑ v, (G * A) u v * omegaStd (x u) (x v) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [omegaStd_sum_smul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [_root_.mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem hermForm_eq_sum {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (H₀ : Matrix (Fin h) (Fin h) ℂ)
    (G : Matrix (Fin 8) (Fin 8) ℤ) (R : Fin 8 → ((Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm z w).im = ∑ i, ∑ j, (G i j : ℝ) * (hermForm H₀ (R i z) (R j w)).im) (z w) :
    hermForm Hm z w = ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w) := by
  refine sub_eq_zero.1 (form_ext s hs
    (fun z w => hermForm Hm z w - ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [hermForm, map_add, add_dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  · intro z w w'
    simp only [hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  · intro c z w
    simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, mul_sub, Finset.mul_sum, mul_left_comm c]
  · intro c z w
    simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.mul_sum, Complex.star_def, Complex.conj_ofReal, mul_left_comm (c : ℂ)]
  · intro z hz w hw
    simp [h0 z hz w hw, Complex.im_sum]

end SharpObj

open SharpObj in

theorem sharpClass_of_unif : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  intro laws laws2 hc hT o _ g k J b em w w' h W a bas σ EF _ _ hw _ hEF t τ m Q Hm ⟨hs, hp⟩ hm hQ
    ⟨_, _, Qspan, _, _, hQim⟩ ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩
  obtain ⟨Ef₀, hEf₀, hbij⟩ := exists_form hs hp
  obtain ⟨P₀, u₀, χ₀, hg, hΛ₀, hAH₀, -, -⟩ := principalTorus_algebraic h _ (imInv τ) Ef₀ (per_lattice hs hp).2.1
    (per_lattice hs hp).2.2 (imInv_isHermitian hp) (imInv_pos hp) hEf₀ hbij
  subst hg
  let R : Fin 8 → (Fin g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  have hRQ : ∀ i x, R i (Q x) = per τ (x i) := fun i x => funext fun j => hQ x i j
  have hmem : ∀ x, per τ x ∈ u₀.Λ := fun x => hΛ₀ ▸ ⟨x, rfl⟩
  have hΛ' : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ := fun z => by
    rw [hΛ, hΛ₀]
    constructor
    · rintro ⟨x, rfl⟩ i
      exact ⟨x i, (hRQ i x).symm⟩
    · intro H
      choose x hx using H
      refine ⟨x, funext fun c => ?_⟩
      obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective c
      exact (hQ x i j).trans (congrFun (hx i) j)
  obtain ⟨pr, hpr, hpru, hprod⟩ := exists_proj laws laws2 hc hT t.pol P₀ u u₀ σ hΛ'
  change Fin 8 → (t.A ⟶ P₀.A) at pr
  change ∀ i, IsMonHom (pr i : t.A ⟶ P₀.A) at hpr
  change ∀ (T : Over (Sp ℂ)) (y : Fin 8 → (T ⟶ P₀.A)), ∃! x : T ⟶ t.A, ∀ i, x ≫ pr i = y i at hprod
  change ∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i at hpru
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hk (by simp [e])
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hWeil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm laws laws2 hc hT P₀ u₀ _ χ₀ hAH₀
  obtain ⟨c, φ, hφ, hcP, ⟨wP, hwP⟩, hlev⟩ := GlobalTheory.T.exists_siegPre_iso_of_polAV laws hc o ℂ em P₀.g k b.ζ (Units.map (em : o →* ℂ) b.ζ) P₀
    (fun x => u₀.ex ((k : ℂ)⁻¹ • per τ (m x))) rfl hk rfl
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em))
    (fun x y => by rw [map_add, map_add, smul_add, u₀.ex_add])
    (fun x => by
      rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul, u₀.ker]
      exact hmem _)
    (fun x y => hWeil k ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ _ hk0 (by
      have e : Ef ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ = omegaStd (m x) (m y) := by
        have := hEf ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩
        rw [im_hermForm_per hs hp] at this
        exact_mod_cast this
      rw [e, hm]
      simp))
  have hform : ∀ z z', hermForm Hm z z' =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm (imInv τ) (R i z) (R j z') :=
    hermForm_eq_sum Hm (imInv τ) (W + W.transpose) R _ Qspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [hQim, hEF, hRQ, im_hermForm_per hs hp, Int.cast_sum, Int.cast_mul])
  have hchi : ∀ l : u.Λ, χ' l = Complex.exp (Real.pi * Complex.I *
      ∑ i, ∑ j, (W i j : ℂ) * ((hermForm (imInv τ) (R i l) (R j l)).im : ℂ)) := fun l => by
    obtain ⟨x, hx⟩ := (hΛ l).1 l.2
    rw [hχ x l hx.symm, hEF, form_act, hw, ← exp_pi_I_int, ← hx]
    simp [hRQ, im_hermForm_per hs hp]
  have hL := GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt laws laws2 hc hT W t.pol u Hm χ' P₀ u₀ _ χ₀ pr R hAH hAH₀ hpru hform hchi
  letI := P₀.isAb.comm
  haveI := hpr
  refine ⟨c, hcP, fun i => pr i ≫ φ.inv, fun i => inferInstanceAs (IsMonHom (pr i ≫ φ.inv)), fun T y => ?_, ?_, fun j i => ?_, fun i v => ?_⟩
  · simp only [← Category.assoc, Iso.comp_inv_eq]
    exact hprod T fun i => y i ≫ φ.hom
  · have hLam : (abelian₂ P₀.A P₀.L).IsLB := DVR.linComb_isLB _ P₀.isLB _ _
    refine LBIso.trans t.isLB (DVR.linComb_isLB _ hLam _ _) (DVR.linComb_isLB _ c.isLB _ _) hL (LBIso.symm ?_)
    have := iso_linComb ((isGen_iff wP).1 hwP) (K := Fin 8 × Fin 8)
      (fun uv => (lift (pr uv.1 ≫ φ.inv) (pr uv.2 ≫ φ.inv)).left) (fun uv => W uv.1 uv.2)
    simp only [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  · obtain ⟨F, hF, hFa⟩ := hact j
    haveI := t.hom j
    have hRF : ∀ z, R i (F z) = ∑ v, a j i v • R v z := fun z => by
      have : ((R i ∘ₗ F).restrictScalars ℝ) = (∑ v, a j i v • R v).restrictScalars ℝ :=
        LinearMap.ext_on_range Qspan fun x => by
          rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hF, hRQ,
            LinearMap.sum_apply]
          simp only [LinearMap.smul_apply, hRQ]
          exact (map_sum (per τ) _ _).trans (Finset.sum_congr rfl fun v _ => map_zsmul (per τ) _ _)
      simpa using LinearMap.congr_fun this z
    have e1 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ t.act j ≫ pr i := fun z => by
      rw [hpru, hFa, Category.assoc]
    have e2 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ ∏ v, pr v ^ a j i v := fun z => by
      rw [hRF, ex_sum, PowMatrixLinear.comp_prod]
      simp only [ex_zsmul, hpru, GrpObj.comp_zpow]
    have e : t.act j ≫ pr i = ∏ v, pr v ^ a j i v :=
      hom_ext_of_lin laws laws2 hc hT t.pol P₀ u u₀ (R i ∘ₗ F) _ _ e1 e2
        (inferInstanceAs (IsMonHom (t.act j ≫ pr i)))
    rw [← Category.assoc, e, PowMatrixLinear.prod_comp]
    simp only [GrpObj.zpow_comp]
    exact (List.prod_ofFn).symm
  · rw [Over.comp_left, hpt, ← Over.comp_left, ← Category.assoc, ← hpru, map_smul, hRQ, ← hlev, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElementStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | exact GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | (intros; apply GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.MulAmple

open GlobalTheory.MulPull GlobalTheory.MulFinite TopologicalSpace

theorem gs_sec_trans {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k k' : H.ι}
    (hk : p z ∈ H.U k) (hk' : p z ∈ H.U k') :
    gs p z (H.U k) (s.f k) =
      (gm p z (H.U k ⊓ H.U k') (H.g k k')).val * gs p z (H.U k') (s.f k') := by
  have hm : p z ∈ H.U k ⊓ H.U k' := ⟨hk, hk'⟩
  exact (gs_res p z _ hm _).symm.trans ((congrArg (gs p z _) (s.compat k k')).trans
    ((gs_mul p z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit p z _ hm _) (gs_res p z _ hm _))))

theorem isUnit_gs_sec {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : p z ∈ H.U k) : IsUnit (gs p z (H.U k) (s.f k)) ↔ p z ∈ Out.nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨k, (isUnit_gs p z _ hk _).1 h⟩, fun h => ?_⟩
  obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 h
  have h' : p z ∈ H.U k' := X.basicOpen_le _ hk'
  rw [gs_sec_trans s p z hk h']
  exact (Units.isUnit _).mul ((isUnit_gs p z _ h' _).2 hk')

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (g h t : Rˣ) (x y : R) (a b : ℕ) :
    (g.val * x) ^ a * (h.val * y) ^ b * ((g ^ a * h ^ b * t)⁻¹).val = x ^ a * y ^ b * (t⁻¹).val := by
  have e : g ^ a * h ^ b * (g ^ a * h ^ b * t)⁻¹ = t⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  have e' : g.val ^ a * h.val ^ b * ((g ^ a * h ^ b * t)⁻¹).val = (t⁻¹).val := congrArg Units.val e
  rw [← e']; ring

theorem exists_fn₂ {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p q : Z ⟶ X) (a b : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h : HasGen H (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)]) (s s' : LB.Sec H) :
    ∃ c : Γ(Z, ⊤), Z.basicOpen c = p ⁻¹ᵁ Out.nonzeroLocus s ⊓ q ⁻¹ᵁ Out.nonzeroLocus s' := by
  obtain ⟨α, hα⟩ := h
  let V : (Fin 2 → H.ι) → Z.Opens := fun j => LB.wchart H (K := Fin 2) ![p, q] j
  have l₁ : ∀ j, V j ≤ p ⁻¹ᵁ H.U (j 0) := fun j z hz => Set.mem_iInter.1 hz 0
  have l₂ : ∀ j, V j ≤ q ⁻¹ᵁ H.U (j 1) := fun j z hz => Set.mem_iInter.1 hz 1
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs p z (H.U (j 0)) (s.f (j 0)) ^ a * gs q z (H.U (j 1)) (s'.f (j 1)) ^ b *
        ((gm (𝟙 Z) z (V j) (α.s j))⁻¹).val := by
    refine ⟨fun j => (p.appLE _ _ (l₁ j)).hom (s.f (j 0)) ^ a *
      (q.appLE _ _ (l₂ j)).hom (s'.f (j 1)) ^ b * (show Γ(Z, V j) from ((α.s j)⁻¹).val), fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·)
      ((gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))) ?_)
    · exact congrArg (· ^ a) (gs_appLE p z _ _ _ hz _)
    · exact congrArg (· ^ b) (gs_appLE q z _ _ _ hz _)
    · exact (gs_unit (𝟙 Z) z _ hz _).trans (congrArg Units.val (map_inv _ _))
  have hex : ∀ z : Z, ∃ j, z ∈ V j := fun z => by
    obtain ⟨k, hk⟩ := exists_chart hH (p z)
    obtain ⟨l, hl⟩ := exists_chart hH (q z)
    refine ⟨![k, l], Set.mem_iInter.2 fun i => ?_⟩
    fin_cases i
    · exact hk
    · exact hl
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => Opens.mem_iSup.2 (hex z)
  obtain ⟨c, hc, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans
        (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      have e := gen_trans hα (𝟙 Z) z (j := j) (j' := j') hz.1 hz.2
      have t : trF (L := H) (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)] (𝟙 Z) z j j' =
          gm p z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ a *
            gm q z (H.U (j 1) ⊓ H.U (j' 1)) (H.g (j 1) (j' 1)) ^ b := by
        rw [trF, Fin.prod_univ_two, ← zpow_natCast, ← zpow_natCast]
        rfl
      rw [t] at e
      rw [hu j z hz.1, hu j' z hz.2, gs_sec_trans s p z (l₁ j hz.1) (l₁ j' hz.2),
        gs_sec_trans s' q z (l₂ j hz.1) (l₂ j' hz.2)]
      exact (congrArg (fun w : (Z.presheaf.stalk z)ˣ => _ * (w⁻¹).val) e).trans
        (units_mul_pow_mul_inv_cancel _ _ _ _ _ a b))
  refine ⟨c, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := hex z
  have k₁ : gs (𝟙 Z) z ⊤ c = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj c).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (hc j))
  refine (isUnit_gs (𝟙 Z) z ⊤ trivial c).symm.trans ?_
  rw [k₁, hu j z hj, Units.isUnit_mul_units, IsUnit.mul_iff, isUnit_pow_iff ha, isUnit_pow_iff hb,
    isUnit_gs_sec s p z (l₁ j hj), isUnit_gs_sec s' q z (l₂ j hj)]
  rfl

theorem hasGen_of_chart {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p : Z ⟶ X) (j₀ : H.ι)
    (h : ∀ z, p z ∈ H.U j₀) : HasGen H (K := Fin 1) ![p] ![1] := by
  have le : ∀ j : Fin 1 → H.ι, LB.wchart H (K := Fin 1) ![p] j ≤ p ⁻¹ᵁ (H.U (j 0) ⊓ H.U j₀) :=
    fun j z hz => ⟨Set.mem_iInter.1 hz 0, h z⟩
  refine ⟨⟨fun j => res (le j) (pullU p _ (H.g (j 0) j₀))⟩, fun j j' => unit_ext fun z hz => ?_⟩
  have v : ∀ j : Fin 1 → H.ι, z ∈ LB.wchart H (K := Fin 1) ![p] j →
      gm (𝟙 Z) z _ (res (le j) (pullU p _ (H.g (j 0) j₀))) =
        gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U j₀) (H.g (j 0) j₀) := fun j hj =>
    (gm_res (𝟙 Z) z (le j) hj _).trans (gm_pull (𝟙 Z) p z _ (le j hj) _)
  refine ((gm_res (𝟙 Z) z _ hz _).trans (v j hz.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb H ![p] ![1] (𝟙 Z) z j j' hz.1 hz.2)
    ((gm_res (𝟙 Z) z _ hz _).trans (v j' hz.2))).trans ?_)
  rw [Fin.prod_univ_one]
  change gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ (1 : ℤ) * _ = _
  rw [zpow_one]
  exact gm_cocycle hH (𝟙 Z ≫ p) z (le j hz.1).1 (le j' hz.2).1 (h z)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow₂ (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1]) (n : ℕ) :
    HasGen L (K := Fin 3) ![x.left, (x⁻¹).left, (x ^ n).left]
      ![(n : ℤ) ^ 2 + n, (n : ℤ) ^ 2 - n, -2] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact (hone.inv.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat, sq])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat])
  | more n ih₀ ih₁ =>
    have hc := hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left
    refine ((hc.mul hc).mul ((ih₁.mul ih₁).mul (ih₀.inv.mul
      ((hone.mul hone).mul (hone.mul hone))))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        (prod_cub (x ^ (n + 1)) x x⁻¹ h) (prod_cub (x ^ (n + 1)) x x⁻¹ h))) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv,
      ofMul_zpow, ofMul_one]
    push_cast
    module

theorem isFinite_pow [IsProper A.hom] [IsAffine S] (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε)
    {I : Type} (s : I → LB.Sec L) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (hs : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite ((𝟙 A) ^ n : A ⟶ A).left := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [pow_one, Over.id_left]; infer_instance
  generalize hm : ((𝟙 A) ^ n : A ⟶ A) = m
  have hw : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hw]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let T : Over S := Over.mk (m.left.fiberι y ≫ A.hom)
  let x : T ⟶ A := Over.homMk (m.left.fiberι y) rfl
  have hxm : x ^ n = x ≫ m := by rw [← hm, MonObj.comp_pow, Category.comp_id]
  have hxi : x⁻¹ = x ≫ GrpObj.inv := rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  obtain ⟨j₁, hj₁⟩ := exists_chart hL ((1 : A ⟶ A).left y)
  have h₀ : HasGen L (K := Fin 1) ![(x ^ n).left] ![1] := hasGen_of_chart hL _ j₀ fun z => by
    rw [hxm]
    exact (congrArg (· ∈ L.U j₀) (hy z)).mpr hj₀
  have h₁ : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1] := hasGen_of_chart hL _ j₁ fun z => by
    have e : (1 : T ⟶ A) = x ≫ m ≫ (1 : A ⟶ A) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [e]
    exact (congrArg (fun w => (1 : A ⟶ A).left w ∈ L.U j₁) (hy z)).mpr hj₁
  have hle : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have h₂ : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left]
      ![((n ^ 2 + n : ℕ) : ℤ), ((n ^ 2 - n : ℕ) : ℤ)] :=
    ((hasGen_pow₂ hL hcube x h₁ n).mul (h₀.mul h₀)).of_formEq hL fun U _ h => by
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul,
        ofMul_zpow, ofMul_one]
      push_cast [hle]
      module
  have key := fun i : I × I => exists_fn₂ hL x.left (x⁻¹).left _ _ (by positivity)
    (by have : n < n ^ 2 := by nlinarith
        omega) h₂ (s i.1) (s i.2)
  choose c hc using key
  have := isAffineHom_fromSpecResidueField A.left y
  have hx : IsAffineHom x.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : A ⟶ A)))
  have hx' : IsAffineHom (x⁻¹).left := by
    rw [hxi, Over.comp_left]; infer_instance
  have hp : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  have hsep : T.left.IsSeparated := by
    have : IsSeparated (m.left.fiberToSpecResidueField y ≫ terminal.from _) := inferInstance
    rw [terminal.comp_from] at this
    exact ⟨this⟩
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y)
    (m.left.fiberToSpecResidueField y) c ?_ fun i => ?_
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (x.left z)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((x⁻¹).left z)))
    exact Opens.mem_iSup.2 ⟨(i, j), (hc (i, j)).ge ⟨hi, hj⟩⟩
  · refine (congrArg IsAffineOpen (hc i)).mpr ?_
    exact ((hs i.1).preimage x.left).inf ((hs i.2).preimage (x⁻¹).left)

end

theorem finite_flat_surjective_pow :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro hl R _ A _ _ hA M hM hamp n hn
  obtain ⟨d, -, m, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A M hM).1 hamp
  have hH := isLB_pw hM d
  have := hA.proper
  have := hA.smooth
  have hcube : HasGen (pw M d) (thφ A (x3 A)) thε :=
    GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hl R A hA ⟨_, hH, m, s, hs⟩ _ hH
  have hf := isFinite_pow hH hcube s hs.1 (fun i => (hs.2 i).1) n hn
  have hm : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := MulN.isMonHom_mulA A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R),
      Flat ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left ∧
        Surjective ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left := fun K _ _ t =>
    flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ A A _ inferInstance
    inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1,
    MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

end GlobalTheory.MulAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_open_integral_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  first | exact @GlobalTheory.Models.nonempty_zOn_of_components | exact GlobalTheory.Models.nonempty_zOn_of_components | (intros; apply GlobalTheory.Models.nonempty_zOn_of_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModel_oneModel_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  first | exact @GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | exact GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | (intros; apply GlobalTheory.Models.System.levelStructureConditions_and_splitFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelObject_fibre_from_complex_charZero : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  first | exact @GlobalTheory.PELFrom.fromC_of_isPEL | exact GlobalTheory.PELFrom.fromC_of_isPEL | (intros; apply GlobalTheory.PELFrom.fromC_of_isPEL <;> assumption)
end

