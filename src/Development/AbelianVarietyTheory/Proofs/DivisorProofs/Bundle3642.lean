import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3639
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3632
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 0 < n → IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  first | exact @GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | exact GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | (intros; apply GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFinRef

theorem exists_dual_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] {a : M} (ha : a ≠ 0) :
    ∃ φ : M →ₗ[ℂ] ℂ, φ a = 1 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ M, φ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff ℂ a).1 h)
  exact ⟨(φ a)⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩

theorem contract_tmul {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (φ : M →ₗ[ℂ] ℂ)
    (a : M) (b : N) : (TensorProduct.lid ℂ N) (φ.rTensor N (a ⊗ₜ b)) = φ a • b := by
  simp

theorem exists_smul_of_tmul_eq {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {a c : M}
    {b d : N} (ha : a ≠ 0) (h : a ⊗ₜ[ℂ] b = c ⊗ₜ[ℂ] d) : ∃ l : ℂ, b = l • d := by
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one ha
  refine ⟨φ c, ?_⟩
  have := congrArg (fun z => (TensorProduct.lid ℂ N) (φ.rTensor N z)) h
  simp only [contract_tmul, hφ, one_smul] at this
  exact this

theorem tensor_eq_zero_of_subsingleton {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Subsingleton M] (z : M ⊗[ℂ] N) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem exists_smul_of_factor {Q Q' Pr Pf Pi : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi]
    (q : Q →ₗ[ℂ] Pr) (q' : Q' →ₗ[ℂ] Pr) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) (hq : Function.Surjective q) (x x' : Pf)
    (a : Q → Pi) (a' : Q' → Pi) (ha : ∀ P, a P = e (q P ⊗ₜ x)) (ha' : ∀ P', a' P' = e (q' P' ⊗ₜ x'))
    (H : (∀ P, a P = 0) ∨ ∃ (P : Q) (P' : Q') (κ : ℂ), a P ≠ 0 ∧ a P = κ • a' P') : ∃ κ : ℂ, x = κ • x' := by
  rcases H with H | ⟨P, P', κ, h0, h1⟩
  ·
    have hPr : Nontrivial Pr := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
      refine hz ?_
      rw [← e.apply_symm_apply z, tensor_eq_zero_of_subsingleton (e.symm z), map_zero]
    obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
    obtain ⟨P, rfl⟩ := hq y
    have h2 : q P ⊗ₜ[ℂ] x = q P ⊗ₜ[ℂ] (0 : Pf) := by
      rw [TensorProduct.tmul_zero]
      apply e.injective
      rw [← ha, H, map_zero]
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨0, by rw [hl, smul_zero, zero_smul]⟩
  · have h2 : q P ⊗ₜ[ℂ] x = q' P' ⊗ₜ[ℂ] (κ • x') := by
      apply e.injective
      rw [← ha, h1, ha', ← LinearEquiv.map_smul, TensorProduct.tmul_smul]
    have hy : q P ≠ 0 := by
      intro h
      exact h0 (by rw [ha, h, TensorProduct.zero_tmul, map_zero])
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨l * κ, by rw [hl, smul_smul]⟩

theorem gBig_mono {Q₁ Q₂ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₂ := by
  obtain ⟨a₁, h₁⟩ := h₁
  refine ⟨a₁, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF hCF
  exact ⟨C₁, x₁, fun C hC D large₂ he hx r T Lc μ hLc G => H G μ C _ _ (h₁ C hC D large₂ he hx r T Lc μ hLc G)⟩

end GlobalTheory.BotFinRef

namespace GlobalTheory.BotFinRef

theorem exists_match_finData : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_mono (GlobalTheory.T.bottom_triangle_finite_factor hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨Pi, rf, rl, p, p', hm, hc⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  refine ⟨Pi, rf, rl, p, p', hm, fun Pr Pf q q' r r' e hq hq' hp hp' => ?_⟩
  haveI : Nontrivial Pi := hm.irred.1
  exact exists_smul_of_factor q q' e hq (r (X.f t)) (r' (X.f' t)) (fun P => p (fockF W.ψ W.θ true FA FW (X.f t) P))
    (fun P' => p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) (hp _ hf) (hp' _ hf') hc

end GlobalTheory.BotFinRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxFamily_movingParts_chain_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  first | exact @GlobalTheory.HSNef.chain_moving_parts | exact GlobalTheory.HSNef.chain_moving_parts | (intros; apply GlobalTheory.HSNef.chain_moving_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charZero : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRhamCharpolyZero.charpoly_push) | (exact GlobalTheory.DeRhamCharpolyZero.charpoly_push) | (intros; apply GlobalTheory.DeRhamCharpolyZero.charpoly_push  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CrysFree

theorem isLocalRing_of_sq {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k) (hπ : Function.Surjective π)
    (hI : RingHom.ker π ^ 2 = 0) : IsLocalRing Λ := by
  have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  haveI := hmax.isPrime
  have hle : RingHom.ker π ≤ nilradical Λ := fun x hx ↦ ⟨2, by
    have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rw [hI] at this; simpa [pow_two] using this⟩
  have heq : nilradical Λ = RingHom.ker π := le_antisymm (nilradical_le_prime _) hle
  haveI : (nilradical Λ).IsMaximal := heq ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical Λ

theorem isDPMorphism_red {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k)
    (hI : RingHom.ker π ^ 2 = 0) : DividedPowers.IsDPMorphism (divided₂ hI) (dp0 k) π := by
  refine (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨?_, fun n hn a ha ↦ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]; intro x hx
    simpa using (RingHom.mem_ker.1 hx)
  · rw [RingHom.mem_ker.1 ha]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (divided₂ hI).dpow_one ha, RingHom.mem_ker.1 ha, (dp0 k).dpow_one (Ideal.zero_mem _)]
    · rw [squareZeroDividedPowers_dpow hI (by omega), map_zero, DividedPowers.dpow_eval_zero _ hn]

theorem mem_smul_top_of_forall {Λ : Type} [CommRing Λ] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module.Finite Λ P] [Module.Free Λ P] (J : Ideal Λ) (h : Module.Dual Λ P) (hh : ∀ c, h c ∈ J) :
    h ∈ J • (⊤ : Submodule Λ (Module.Dual Λ P)) := by
  classical
  let b := Module.Free.chooseBasis Λ P
  rw [← b.sum_dual_apply_smul_coord h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hh _) Submodule.mem_top

end GlobalTheory.CrysFree

namespace GlobalTheory.CrysFree

theorem crys_free_and_red : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  intro F _ _ Λ _ k _ π hπ hI A₀ _ _ hA₀ a
  haveI := isLocalRing_of_sq π hπ hI
  letI : Algebra Λ k := π.toAlgebra
  obtain ⟨A, _, i, h, hA⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine Λ (RingHom.ker π) hI k π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Λ A hA
  obtain ⟨HFree, -, HBC, HRigid, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hrig := HRigid Λ A g hA hg (RingHom.ker π) (divided₂ hI) (isDPNilpotent_squareZero hI) k π hπ rfl A₀ i h
  let e : primDR A ≃ₗ[Λ] prim (divided₂ hI) (spMap π) A₀ :=
    LinearEquiv.ofBijective (liftMor (divided₂ hI) h).pull hrig
  obtain ⟨hfin, hproj, -⟩ := HFree.prim hA hg
  haveI : Module.Finite Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Finite.equiv e
  haveI : Module.Projective Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Projective.of_equiv e
  haveI := Module.finitePresentation_of_projective Λ (prim (divided₂ hI) (spMap π) A₀)
  haveI : Module.Free Λ (prim (divided₂ hI) (spMap π) A₀) := Module.free_of_flat_of_isLocalRing
  have m : GrpMor (divided₂ hI) (spMap π) A₀ (dp0 k) (𝟙 _) A₀ (algebraMap Λ k) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
    GrpMor.of_hom (isDPMorphism_red π hI) (Category.id_comp _).symm (𝟙 A₀)
  have hm : m.IsBC := by
    have hb := (HBC Λ A g hA hg k A₀ i h).1
    let E := LinearEquiv.baseChange Λ k _ _ e
    have key : liftSemi m.pull ∘ₗ E.toLinearMap =
        liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.baseChange_tmul,
          liftSemi_tmul]
        congr 1
        exact GrpMor.pull_pull (liftMor (divided₂ hI) h) m (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h)
          (fun _ ↦ rfl) (by simp) c
      | add x y hx hy => rw [map_add, hx, hy, map_add]
    have : liftSemi m.pull = liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull ∘ₗ
        E.symm.toLinearMap := by
      rw [← key, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; rfl
    unfold GrpMor.IsBC
    rw [this]
    exact hb.comp E.symm.bijective
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hact : ∀ (o : 𝓞 F) (x : Crys (divided₂ hI) (spMap π) A₀),
      hm.bcMap (act (divided₂ hI) (spMap π) a o x) = act (dp0 k) (𝟙 _) a o (hm.bcMap x) := by
    intro o x
    haveI := a.hom o
    rw [act_apply, act_apply]
    exact hm.corr_iff.1 (GrpMor.Corr.push (m := m) m (a.act o) (a.act o) (by simp) (hm.corr_iff.2 rfl))
  letI := tensorModule (divided₂ hI) (spMap π) a
  letI := tensorModule (dp0 k) (𝟙 _) a
  refine ⟨{ toFun := hm.bcMap, map_add' := hm.bcMap.map_add, map_smul' := ?_ }, ?_, ?_⟩
  · intro r x
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul l o =>
      have e1 : (l ⊗ₜ[ℤ] o) • x = l • act (divided₂ hI) (spMap π) a o x := rfl
      have e2 : ∀ y : HdR A₀, ((Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom
          (l ⊗ₜ[ℤ] o)) • y = π l • act (dp0 k) (𝟙 _) a o y := fun y ↦ rfl
      rw [e1, e2, hm.bcMap.map_smulₛₗ, hact]
      rfl
    | add r s hr hs =>
      rw [add_smul, hm.bcMap.map_add, hr, hs, map_add, add_smul]
  · intro h'
    let l : prim (divided₂ hI) (spMap π) A₀ →ₗ[Λ] k :=
      { toFun c := h' (m.pull c)
        map_add' c d := by rw [map_add, map_add]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh, hhl⟩ := Module.projective_lifting_property (Algebra.linearMap Λ k) l hπ
    exact ⟨hh, hm.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc : m.Corr x 0 := hm.corr_iff.2 hx
    exact mem_smul_top_of_forall _ x fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))

end GlobalTheory.CrysFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToIntegerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_up_to_integer : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  first | (exact @GlobalTheory.AV.AbVar.exists_isAdj) | (exact GlobalTheory.AV.AbVar.exists_isAdj) | (intros; apply GlobalTheory.AV.AbVar.exists_isAdj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.SharpPull
namespace GlobalTheory.KthRoot

theorem finite_flat_surjective_mulN_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro S A _ hA n hn
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := GlobalTheory.MulFlatSurj.mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

theorem exists_descent_mulN : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (h : A ⟶ D) (k : ℕ) (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left), IsAbelianScheme A → IsMonHom h → 0 < k → IsGrpPullback AU A t φ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y ∧ (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left := by
  intro Y A D _ _ _ h k U t AU _ _ φ hA hh hk hpb hker
  have hAU : IsAbelianScheme AU := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hψ := isGrpPullback_pullback D t
  obtain ⟨hU, ehU⟩ := GlobalTheory.SharpPull.exists_lift hpb hψ h
  have : IsMonHom hU := GlobalTheory.SharpPull.isMonHom_lift hpb hψ ehU
  obtain ⟨hfin, hflat, hsurj⟩ := finite_flat_surjective_mulN_any U AU hAU k hk
  have hmon : IsMonHom (mulN AU k) := by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow]
    exact GlobalTheory.AbLaw.MulN.isMonHom_mulA AU k
  obtain ⟨⟨y, hy, hyk⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective U AU AU _ (mulN AU k) hU hmon
    inferInstance hflat hsurj inferInstance (fun T x hx => by
      apply GlobalTheory.SharpPull.push_inj hψ
      rw [GlobalTheory.SharpPull.push_comp hpb hψ ehU, map_one]
      refine hker (Over.mk (T.hom ≫ t)) T.hom rfl _ ?_
      have ex : x ^ k = x ≫ mulN AU k := by
        rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
      rw [← map_pow, ex, hx, map_one])
  exact ⟨y, hy, by rw [hyk, ehU]⟩

theorem exists_birigid_root_of_descent : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → ∀ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y → (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hQ hadd hM hiso U t AU _ _ φ φ₂ hpb hsq y hy hyk
  have hψ := isGrpPullback_pullback D t
  let W : Over U := AU ⊗ AU
  let a₁ : Over.mk (W.hom ≫ t) ⟶ A := pushHom hpb W (fst AU AU)
  let d : Over.mk (W.hom ≫ t) ⟶ D := pushHom hψ W (snd AU AU ≫ y)
  let P : LB (G2 AU).left := Q.pull (lift a₁ d).left
  have hP : P.IsLB := pull_isLB hQ.isLB _

  have key : ∀ (T : Over U) (z : T ⟶ W), CechPic.pull z.left (cls P hP) =
      evc hQ.isLB (pushHom hpb T (z ≫ fst AU AU)) (pushHom hψ T (z ≫ snd AU AU ≫ y)) := by
    intro T z
    rw [cls_pull hQ.isLB, ← pull_comp, evc]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst]
      rfl
    · rw [Category.assoc, lift_left_snd, lift_left_snd]
      rfl

  refine ⟨P, hP, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, ?_⟩
  · rw [cls_pull hP, key, lift_fst, map_one]
    exact hQ.additive.evc_one hQ.isLB _
  · rw [cls_pull hP, key, lift_snd_assoc, MonObj.one_comp, map_one]
    exact evc_one_right hQ.isLB hQ.zero _
  · have hs : (swap Q).IsLB := pull_isLB hQ.isLB _
    have add2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u v : Z ⟶ D),
        evc hQ.isLB a (u * v) = evc hQ.isLB a u + evc hQ.isLB a v := by
      intro Z a u v
      rw [← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs]
      exact (isAdditive_iff hs).1 hadd Z u v a
    have pow2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u : Z ⟶ D) (n : ℕ),
        evc hQ.isLB a (u ^ n) = n • evc hQ.isLB a u := by
      intro Z a u n
      induction n with
      | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQ.isLB hQ.zero a
      | succ n ih => rw [pow_succ, add2, ih, succ_nsmul]
    have ep : (𝟙 W ≫ snd AU AU ≫ y) ^ k = snd AU AU ≫ mulN AU k ≫ y := by
      rw [Category.id_comp, ← MonObj.comp_pow, GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.pow_comp, Category.id_comp]
    have e1 : cls P hP = CechPic.pull (𝟙 W : W ⟶ W).left (cls P hP) := by rw [Over.id_left, pull_id]
    refine (cls_eq_iff (pull_isLB hM _) (isLB_lbPow hP k)).1 ?_
    rw [cls_lbPow hP, e1, key, ← pow2, ← map_pow, cls_pull hM, pull_comp, ← cls_pull hM c (pull_isLB hM c),
      (cls_eq_iff (pull_isLB hM c) (pull_isLB hQ.isLB _)).2 hiso, cls_pull hQ.isLB, evc, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst, push_left, hsq.1, Category.id_comp]
    · rw [Category.assoc, lift_left_snd, lift_left_snd, push_left, ep, Over.comp_left, Over.comp_left,
        Category.assoc, hyk, ← Category.assoc, hsq.2, Category.assoc]

theorem exists_birigid_kth_root : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hA hD hQ hadd hh hk hku hM hiso U t AU _ _ φ φ₂ hpb hsq hker
  obtain ⟨y, hy, hyk⟩ := exists_descent_mulN Y A D h k U t AU φ hA hh hk hpb hker
  exact exists_birigid_root_of_descent Y A D Q h k X M c hQ hadd hM hiso U t AU φ φ₂ hpb hsq y hy hyk

end GlobalTheory.KthRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  first | exact @GlobalTheory.TChart.exists_degFrom_of_trait | exact GlobalTheory.TChart.exists_degFrom_of_trait | (intros; apply GlobalTheory.TChart.exists_degFrom_of_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  first | exact @GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | exact GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | (intros; apply GlobalTheory.Poinc.Sep.exists_chartMember_traitsR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHeatOperatorsAbelianLocusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_heatOperators_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) := by
  first | exact @GlobalTheory.HeatV.exists_heat_abLocus | exact GlobalTheory.HeatV.exists_heat_abLocus | (intros; apply GlobalTheory.HeatV.exists_heat_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.SiegUniqBase

section FlatPow
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

theorem flat_surjective_qc_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ k : ℕ, 0 < k → Flat ((𝟙 A) ^ k).left ∧ Surjective ((𝟙 A) ^ k).left ∧ QuasiCompact ((𝟙 A) ^ k).left := by
  intro S A _ hA k hk
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA k hk
  have e : (𝟙 A) ^ k = ReciprocityTheory.ChartRestriction.G.Out.mulA A k := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A k)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ k) hf).2

end FlatPow

end GlobalTheory.UPel.HT.SiegUniqBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_crystal_action_adjoint : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (c : D.O) x y, φ (GlobalTheory.HTCount.crysAct o₀ c x) y = φ x (GlobalTheory.HTCount.crysAct o₀ (D.star c).unop y) := by
  first | (exact @GlobalTheory.HTCount.crysAct_adjoint) | (exact GlobalTheory.HTCount.crysAct_adjoint) | (intros; apply GlobalTheory.HTCount.crysAct_adjoint  <;> assumption)
end

