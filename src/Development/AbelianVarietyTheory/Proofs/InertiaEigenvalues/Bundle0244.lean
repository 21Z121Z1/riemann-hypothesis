import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport
section
namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem act_root_eq_pow_of_chi_nat {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (u : ℕ)
    (hg : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ u := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ
  rw [hg] at ha
  have h2 : ‖((((u : ℤ) - (a : ℤ) : ℤ)) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    push_cast; exact ha
  have h3 : ((l : ℤ) ^ m) ∣ ((u : ℤ) - (a : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mp h2
  have h4 : a ≡ u [MOD l ^ m] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact h3
  rw [hga, pow_eq_pow_mod a hζ, pow_eq_pow_mod u hζ, h4]

theorem actT_εroot_eq_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l)
    (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) →
      ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  intro l _ P AI g u hg j
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  refine Perfection.ext fun n => ?_
  have hc : PreTilt.coeff n (AI.εroot j) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + j)) := by
    rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g _ n _ hc
  have h3 : y' = AI.ζ (n + j) ^ u := by
    apply Subtype.ext
    rw [h1, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext,
      act_root_eq_pow_of_chi_nat P g u hg (n + j) _ (hz _)]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h2, map_pow, hc, h3]
  exact map_pow _ _ _

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_v_of_norm_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (hx : ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ))) :
    ((k : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlk : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero k hl
  have hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]
    exact hx
  obtain ⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by
    refine ⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩
    show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)
    field_simp
  have hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL := by
    have e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y := rfl
    rw [e]
    exact (OL LL).algebraMap_mem y
  have hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l])) := (P.27 LL _).2 hmem
  have hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  rw [hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]
  exact le_add_of_nonneg_right hv0

theorem grp_GKs_H : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  intro l _ P _ K s LL _ W hW g
  have hcyc : IsCyc P.χQ := P.20
  have hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := P.PD_χ K g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · unfold Gj at hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) s
    have hmem : ζ ∈ Ks K s := by
      unfold Ks
      exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _)
        (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)
    have hfix : (g : GQ l) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) :=
      hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix
    have hv := le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn
    have e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 =
        algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1) := by
      rw [hχ, map_sub, map_one]
    rw [W.GKs_def g, hW, e]
    exact_mod_cast hv
  · unfold Hinf at hg
    have hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      intro m
      refine (hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)
      have hmem : ζ ∈ Kinf K := by
        unfold Kinf
        exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _)
          (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      by_contra hne
      have hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd (hall m) (not_le.2 hm)
    have h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1 := by
      rw [W.χΓ_res g, hχ, h1, map_one]
    have h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := Subtype.ext h2
    have h4 : W.χΓ (W.resΓ g) = 1 := Units.val_eq_one.1 h3
    exact W.χΓ_inj (by rw [h4, map_one])

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEqStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_invariants_coordinates_finrank_eq : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  first | exact @GlobalTheory.deRham_invariants_coord_finrank | exact GlobalTheory.deRham_invariants_coord_finrank | (intros; apply GlobalTheory.deRham_invariants_coord_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionFrameOfMatrixForm
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem act_eq_of_mem_intC {l : ℕ} [Fact l.Prime]
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ intC F) : act σ y = y := by
  simp only [intC, inC, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe] at hy
  obtain ⟨⟨x, hxF, rfl⟩, -⟩ := hy
  rw [ha.1 σ x, (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ x hxF]

theorem isDec_of_matrix : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  intro l _ act χ K m d M D g ha hg hMc hMmul hMfix hD hDinv hInt hH hgclose
  obtain ⟨Y, hY, hDY⟩ := hDinv
  have hl : (l : PadicComplex l) ≠ 0 := by
    exact_mod_cast (Fact.out : l.Prime).ne_zero

  have hright : D * ((l : PadicComplex l)⁻¹ • Y) = 1 := by
    rw [Matrix.mul_smul, hDY, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hdet : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hright
  have hinv : D⁻¹ = (l : PadicComplex l)⁻¹ • Y := Matrix.inv_eq_right_inv hright
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hdet
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdet

  have hmapmul : ∀ (e : PadicComplex l ≃+* PadicComplex l) (A B : Matrix (Fin d) (Fin d) (PadicComplex l)),
      (A * B).map e = A.map e * B.map e := by
    intro e A B
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  have hmapcomp : ∀ σ τ : GQ l, D.map (act (σ * τ)) = (D.map (act τ)).map (act σ) := by
    intro σ τ
    ext i j
    simp only [Matrix.map_apply, map_mul]
    rfl

  refine ⟨fun σ => D⁻¹ * (M σ * D.map (act σ)), hdet, hD, ?_, ⟨hg, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rw [hinv, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]
    exact hY a b
  · intro a b
    simp only [Matrix.mul_apply, Matrix.map_apply]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hMc k j).mul ?_
    exact (IsActC.continuous_orbit l act ha (D j b)).continuousOn
  · intro σ hσ a b
    obtain ⟨X, hX, hMX⟩ := hInt σ hσ
    show (D⁻¹ * (M σ * D.map (act σ))) a b ∈ intC (Ks K m)
    rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    exact hX a b
  · intro σ hσ τ hτ
    obtain ⟨X, hX, hMX⟩ := hInt τ hτ
    have hUτ : D⁻¹ * (M τ * D.map (act τ)) = X := by
      rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

    have hXfix : X.map (act σ) = X := by
      ext i j
      exact act_eq_of_mem_intC ha (show σ ∈ (Ks K m).fixingSubgroup from hσ) (hX i j)
    show D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
      = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ)))
    calc D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
        = D⁻¹ * (M σ * (M τ * D.map (act τ)).map (act σ)) := by
          rw [hMmul σ hσ τ hτ, hmapmul, hMfix σ hσ τ hτ, hmapcomp]
          simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (M σ * (D.map (act σ) * X)) := by rw [hMX, hmapmul, hXfix]
      _ = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ))) := by
          rw [hUτ]
          simp only [Matrix.mul_assoc]
  · intro σ hσ
    show D⁻¹ * (M σ * D.map (act σ)) = 1
    rw [hH σ hσ, hDD]
  · intro a b
    obtain ⟨X, hX, hMX⟩ := hgclose
    have hU : D⁻¹ * (M g * D.map (act g)) - 1 = X := by
      rw [← hDD, ← Matrix.mul_sub, hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    show ‖(D⁻¹ * (M g * D.map (act g)) - 1) a b‖ < rho1 l
    rw [hU]
    exact hX a b
  · intro σ hσ
    show D * (D⁻¹ * (M σ * D.map (act σ))) = M σ * D.map (act σ)
    rw [← Matrix.mul_assoc, hDD', Matrix.one_mul]

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DependentOfCardLe
section
open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

namespace GlobalTheory.Cyc.CocycleCount

theorem dependent_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ψ : G →* ℤ_[l]ˣ) (C n : ℕ), (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ C * l ^ (r * n)) → ∀ z : Fin (n + 1) → G → ℚ_[l], (∀ i, Continuous (z i)) → (∀ i g h, z i (g * h) = z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * z i h) → ∃ c : Fin (n + 1) → ℚ_[l], c ≠ 0 ∧ ∀ g, ∑ i, c i * z i g = 0 := by
  intro l _ G _ _ _ _ ψ C n hC z hz hcoc
  have hl : l.Prime := Fact.out
  by_contra hne
  push Not at hne

  obtain ⟨B, hB⟩ := (isCompact_range (continuous_pi hz : Continuous fun g i => z i g)).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max B 1)⁻¹) (by positivity)
  have ha1 : ∀ i g, ‖a * z i g‖ ≤ 1 := fun i g => by
    rw [norm_mul]
    have h1 : ‖z i g‖ ≤ max B 1 :=
      ((norm_le_pi_norm (fun i => z i g) i).trans (hB _ ⟨g, rfl⟩)).trans (le_max_left _ _)
    calc ‖a‖ * ‖z i g‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  let w : Fin (n + 1) → G → ℤ_[l] := fun i g => ⟨a * z i g, ha1 i g⟩
  have hw : ∀ i, Continuous (w i) := fun i => (continuous_const.mul (hz i)).subtype_mk _
  have hwc : ∀ i g h, w i (g * h) = w i g + (ψ g : ℤ_[l]) * w i h := fun i g h => Subtype.ext (by
    change a * z i (g * h) = a * z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * (a * z i h)
    rw [hcoc]; ring)
  let W : Fin (n + 1) → C(G, ℚ_[l]) := fun i => ⟨fun g => a * z i g, continuous_const.mul (hz i)⟩
  let L : (Fin (n + 1) → ℚ_[l]) →ₗ[ℚ_[l]] C(G, ℚ_[l]) := Fintype.linearCombination ℚ_[l] W
  have hL : ∀ c g, L c g = ∑ i, c i * (a * z i g) := fun c g => by
    simp [L, W, Fintype.linearCombination_apply, ContinuousMap.sum_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    obtain ⟨g, hg⟩ := hne c h0
    apply hg
    have h1 := hL c g
    rw [hc, ContinuousMap.zero_apply] at h1
    apply mul_left_cancel₀ ha'
    rw [mul_zero, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (K : ℝ) hl1
  have key : ∀ r : ℕ, 0 < r → l ^ r ≤ C * l ^ (v * n) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := hC (r + v) (by omega)
    let F : (Fin (n + 1) → Fin (l ^ r)) →
        ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ (r + v))) := fun c =>
      ⟨fun g => PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g),
        (continuous_toZModPow _).comp
          (continuous_finset_sum _ fun i _ => continuous_const.mul (hw i)), fun g h => by
        rw [ReciprocityTheory.Gal.charRep_apply, redChar_apply, ← map_mul, ← map_add, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine congrArg (PadicInt.toZModPow (r + v)) ?_
        exact Finset.sum_congr rfl fun i _ => by rw [hwc]; ring⟩
    have hF : Function.Injective F := by
      intro c c' h
      let d : Fin (n + 1) → ℚ_[l] := fun i => ((((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) : ℤ) : ℚ_[l])
      have h1 : ‖L d‖ ≤ (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by
        rw [ContinuousMap.norm_le _ (by positivity)]
        intro g
        have h2 : PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g) =
            PadicInt.toZModPow (r + v) (∑ i, ((c' i : ℕ) : ℤ_[l]) * w i g) :=
          congrFun (congrArg Subtype.val h) g
        rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
          ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def] at h2
        refine le_of_eq_of_le (congrArg norm ?_) h2
        rw [hL, ← Finset.sum_sub_distrib]
        refine Eq.trans ?_ (map_sum (PadicInt.Coe.ringHom (p := l)) _ _).symm
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = ((((c i : ℕ) : ℤ_[l]) * w i g - ((c' i : ℕ) : ℤ_[l]) * w i g : ℤ_[l]) : ℚ_[l])
        have hwv : ((w i g : ℤ_[l]) : ℚ_[l]) = a * z i g := rfl
        rw [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast,
          PadicInt.coe_natCast, hwv]
        simp only [d, Int.cast_sub, Int.cast_natCast]
        ring
      have h3 : ‖d‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
        have h4 := ZeroHomClass.bound_of_antilipschitz L hK d
        calc ‖d‖ ≤ K * ‖L d‖ := h4
          _ ≤ (l : ℝ) ^ v * (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by gcongr
          _ = _ := by
            rw [← zpow_natCast, ← zpow_add₀ (by positivity)]
            congr 1
            push_cast; ring
      funext i
      have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) _ r).1 ((norm_le_pi_norm d i).trans h3)
      apply Fin.ext
      have h6 : ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h5
        have e1 : ((c i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c i).2
        have e2 : ((c' i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c' i).2
        rw [abs_lt]
        constructor <;> omega
      omega
    have h7 := (Nat.card_le_card_of_injective F hF).trans hcard
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin] at h7
    have h8 : l ^ r * l ^ (r * n) ≤ (C * l ^ (v * n)) * l ^ (r * n) := by
      calc l ^ r * l ^ (r * n) = (l ^ r) ^ (n + 1) := by ring
        _ ≤ _ := h7
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h8 (pow_pos hl.pos _)
  have h9 := key (C * l ^ (v * n) + 1) (Nat.succ_pos _)
  have h10 : C * l ^ (v * n) + 1 < l ^ (C * l ^ (v * n) + 1) := Nat.lt_pow_self hl.one_lt
  omega

end GlobalTheory.Cyc.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DictKFree
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

theorem dict_K_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; (ell S = 2 → ∃ i : S.K, i ^ 2 = -1) → ∀ (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L), IsSESLat (Qp := S.Qp) ι π → ∀ (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : S.W.DD Yt), (z : Z.V) = π.f yt → E.jD Z (S.W.map π e) = (1 : S.RW) ⊗ₜ[S.O] z → (∀ δ ∈ S.W.DelF, S.W.γD Yt δ e = e) → ∀ pr : ↥(S.W.wachCocyclesDelta T), S.W.map ι (pr : S.W.DD T × S.W.DD T).1 = S.W.φD Yt e - e → S.W.map ι (pr : S.W.DD T × S.W.DD T).2 = S.W.γD Yt S.W.gamK e - e → ∀ c : ↥(latticeCocycles T.L), (∀ g : S.G, ι.f ((c : S.G → T.V) g) = Yt.ρ g yt - yt) → S.W.clK T pr = Submodule.Quotient.mk c := by
  intro D HW F l _ K s LL h S E hi T Yt Z ι π hs yt z e hz he hδ pr h1 h2 c hc
  have hp : ell S = l := (D.loc l).PD_p K
  have hG : l = 2 → GK K ≤ Gj K 2 := fun hl => by
    obtain ⟨i, hi⟩ := hi (hp.trans hl)
    exact localGalois_le_cyclotomicLevelTwo_of_sqrt_neg_one K hl i hi
  haveI : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  haveI : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact dict_of_dense S E (algebraMap_RW_injective LL)
    (fun hl => DelF_eq_one (D.loc l) S.W (D.locA l) hG (hp.symm.trans hl))
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) hG) T Yt Z ι π hs yt z e hz he hδ pr h1 h2 c hc

end GlobalTheory.ExtDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.FinExtIntegers

theorem dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro l _ LL
  unfold OL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsScalarTower ℤ_[l] ℚ_[l] ↥LL.1 := inferInstance
  have hfin : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : FaithfulSMul ℤ_[l] ↥LL.1 := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥LL.1
  have hdvr : IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥LL.1) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥LL.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥LL.1
  refine ⟨hdvr, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _, ?_⟩
  intro hu
  have hl : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  apply hl
  apply (isUnit_map_iff (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) _).mp
  simpa using hu

end GlobalTheory.FinExtIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMulStatement
section
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e → ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧ (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  first | exact @GlobalTheory.PeriodSol.period_solution | exact GlobalTheory.PeriodSol.period_solution | (intros; apply GlobalTheory.PeriodSol.period_solution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  first | exact @GlobalTheory.Cyc.isMat_exists_and_props | exact GlobalTheory.Cyc.isMat_exists_and_props | (intros; apply GlobalTheory.Cyc.isMat_exists_and_props <;> assumption)
end

