import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightModuleUnitaryForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeKeep

variable {D : D7} {V : HSp D}

theorem suppF_iff (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem mt_mul (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := rfl

theorem mt_one : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem fix_mul {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : f • (b - 1) = b - 1) : f • (a * b - 1) = a * b - 1 := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by rw [sub_mul, one_mul]; abel
  rw [e, smul_add, hb, ← smul_mul_assoc, ha]

theorem fix_inv {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : a * b = 1) : f • (b - 1) = b - 1 := by
  have e : b - 1 = -((a - 1) * b) := by rw [sub_mul, one_mul, hb, neg_sub]
  rw [e, smul_neg, ← smul_mul_assoc, ha]

theorem suppF_mul {f : Formalism.L2.Theta.AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  rw [suppF_iff] at ha hb ⊢
  rw [mt_mul]
  exact fix_mul ha hb

theorem suppF_inv {f : Formalism.L2.Theta.AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  rw [suppF_iff] at ha ⊢
  exact fix_inv ha (by rw [← mt_mul, mul_inv_cancel, mt_one])

theorem suppF_one (f : Formalism.L2.Theta.AE D) : SuppF V f 1 := by
  rw [suppF_iff, mt_one, sub_self, smul_zero]

theorem exists_loc (V : HSp D) (f : Formalism.L2.Theta.AE D) : ∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g :=
  ⟨{ carrier := {g | SuppF V f g}, mul_mem' := suppF_mul, one_mem' := suppF_one f, inv_mem' := suppF_inv },
    fun _ => Iff.rfl⟩

end GlobalTheory.HeckeKeep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialAction
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame

theorem map_mk_smul_sum {O A : Type} [CommRing O] [Ring A] [Algebra O A] {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W] (U : Submodule A V)
    (ψ : U →ₗ[A] W) {κ : Type} (S : Finset κ) (c : O) (v : κ → V) (hv : ∀ s, v s ∈ U) (x : V) (hx : x ∈ U)
    (e : x = c • ∑ s ∈ S, v s) : c • ∑ s ∈ S, ψ ⟨v s, hv s⟩ = ψ ⟨x, hx⟩ := by
  have e' : (⟨x, hx⟩ : U) = c • ∑ s ∈ S, (⟨v s, hv s⟩ : U) := by
    apply Subtype.ext
    simpa using e
  rw [e', LinearMap.map_smul_of_tower, map_sum]

section
variable {O A G I : Type} [CommRing O] [Ring A] [Algebra O A] [Group G] (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A)
  (tr : I → Finset G) (cst : I → O)

theorem hecke_values_mem {V : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule A V) (t : MvPolynomial I O) :
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ U) →
      ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f hf g
    rw [hV.1 c f]
    exact U.smul_of_tower_mem c (hf g)
  | add p q hp hq =>
    intro f hf g
    rw [add_smul]
    exact U.add_mem (hp f hf g) (hq f hf g)
  | mul_X p i hp =>
    intro f hf g
    rw [mul_smul]
    apply hp
    intro g'
    rw [hV.2 i f g']
    exact U.smul_of_tower_mem _ (U.sum_mem fun s _ => hf _)

theorem hecke_values_map {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s))
    (U : Submodule A V)
    (ψ : U →ₗ[A] W) (t : MvPolynomial I O) :
    ∀ (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
      (hf : ∀ g, (f : G → V) g ∈ U), (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
      ∀ g (h : ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
        ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨_, h⟩ := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f φ hf hφ g h
    have e : (⟨_, h⟩ : U) = c • ⟨(f : G → V) g, hf g⟩ := by
      apply Subtype.ext
      simp only [hV.1 c f]
      rfl
    rw [e, LinearMap.map_smul_of_tower, ← hφ g, hW.1 c φ]
    rfl
  | add p q hp hq =>
    intro f φ hf hφ g h
    have hp' := hecke_values_mem Γ jK tr cst hV U p f hf g
    have hq' := hecke_values_mem Γ jK tr cst hV U q f hf g
    have e : (⟨_, h⟩ : U) = ⟨_, hp'⟩ + ⟨_, hq'⟩ := by
      apply Subtype.ext
      simp only [add_smul]
      rfl
    rw [e, map_add, ← hp f φ hf hφ g hp', ← hq f φ hf hφ g hq', add_smul]
    rfl
  | mul_X p i hp =>
    intro f φ hf hφ g h
    have hX := hecke_values_mem Γ jK tr cst hV U (X i) f hf
    have hφX : ∀ g', (((X i : MvPolynomial I O) • φ : Forms O Γ jK W) : G → W) g' = ψ ⟨_, hX g'⟩ := by
      intro g'
      refine (hW.2 i φ g').trans (Eq.trans ?_ (map_mk_smul_sum U ψ (tr i) (cst i) (fun s => (f : G → V) (g' * s))
        (fun s => hf _) _ (hX g') (hV.2 i f g')))
      exact congrArg (fun z => cst i • z) (Finset.sum_congr rfl fun s _ => hφ (g' * s))
    have h2 : ((p • ((X i : MvPolynomial I O) • f) : Forms O Γ jK V) : G → V) g ∈ U := by
      rw [← mul_smul]
      exact h
    have e : (⟨_, h⟩ : U) = ⟨_, h2⟩ := by
      apply Subtype.ext
      simp only [mul_smul]
    rw [e, mul_smul]
    exact hp _ _ hX hφX g h2

theorem hecke_stable_nat (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s)) :
    HeckeStable O Γ jK (MvPolynomial I O) V ∧ HeckeNat O Γ jK (MvPolynomial I O) V W :=
  ⟨fun U t f hf => hecke_values_mem Γ jK tr cst hV U t f hf,
    fun U ψ t f φ hf hf' hφ g => hecke_values_map Γ jK tr cst hV hW U ψ t f φ hf hφ g (hf' g)⟩

end

set_option maxHeartbeats 1000000 in

theorem heckeStable_heckeNat_of_isHecke : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  intro l _ ι _ _ N F lam jK i1 W i2 i3 i4 i5 i6 hV hW
  refine @hecke_stable_nat F.O (alg F.O N lam) F.G F.I _ _ _ _ F.Γ F.K jK F.tr F.cst (NablaT F.O N lam) W _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact hV
  · exact hW

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosetsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTestProduct_support_finite_leftCosets : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  first | exact @GlobalTheory.testProd_support_finite | exact GlobalTheory.testProd_support_finite | (intros; apply GlobalTheory.testProd_support_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatVacSign

variable {D : D7} {S T : HSp D}

theorem cA_incA' (w : D.host.E) : cA D (incA D w) = incA D (star w) := rfl

theorem hO_smul_smul (c c' : AE D) (x y : WO S T) :
    hO S T (c • x) (c' • y) = c * cA D c' * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symplO_smul_smul (w w' : D.host.E) (x y : WO S T) :
    symplO S T (incA D w • x) (incA D w' • y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * (w * star w')) * hO S T x y) := by
  rw [symplO, hO_smul_smul, cA_incA', map_mul (incA D), map_mul (incA D)]
  congr 1
  ring

theorem symplOH_smul_norm {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) (x y : WO S T) :
    symplOH S T (incA D w • x) (incA D w • y) = (n : AF D.host.F) * symplO S T x y := by
  have e : incA D (D.host.xi0 * (w * star w)) * hO S T x y =
      ((2 * n : ℤ) : AE D) * (incA D D.host.xi0 * hO S T x y) := by
    rw [hw]
    simp only [map_mul, map_intCast, map_ofNat]
    push_cast
    ring
  rw [symplOH, symplO_smul_smul, e, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, ← symplO]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  push_cast
  linear_combination ((n : AF D.host.F) * symplO S T x y) * h2

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem char_symplOH_smul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) {x y : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplOH S T (incA D w • x) (incA D w • y)) = 1 := by
  rw [symplOH_smul_norm hw, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow,
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hx hy, _root_.one_zpow]

theorem incA_smul_finTens {m k : ℕ} (w : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin k) D.host.E) :
    incA D w • GlobalTheory.LatVac.finTens α M = GlobalTheory.LatVac.finTens α (w • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] w : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j) =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (w * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO' {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True)
    ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (GlobalTheory.LatVac.smul_mem_latRat w hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

def fixGroup (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (c : AE D)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f}
  zero_mem' := ⟨zero_mem _, fun f _ => by rw [smul_zero, GlobalTheory.LatVac.heisO_zero]⟩
  add_mem' := by
    rintro a b ⟨ha, fa⟩ ⟨hb, fb⟩
    refine ⟨add_mem ha hb, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • a) (c • b) f
    rw [fb f hf, fa f hf, hΛ a ha b hb, one_smul, ← smul_add] at h1
    exact h1.symm
  neg_mem' := by
    rintro a ⟨ha, fa⟩
    refine ⟨neg_mem ha, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • -a) (c • a) f
    rw [fa f hf, hΛ (-a) (neg_mem ha) a ha, one_smul, ← smul_add, neg_add_cancel,
      smul_zero, GlobalTheory.LatVac.heisO_zero] at h1
    exact h1

theorem mem_fixGroup {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {c : AE D}
    {hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1} {u : WO S T} :
    u ∈ fixGroup ψ Λ c hΛ ↔ u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f := Iff.rfl

theorem heisO_smul_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (w : 𝓞 D.host.E) {n : ℤ} (hw : (w : D.host.E) * star (w : D.host.E) = 2 * n)
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    heisO ψ S T (incA D (w : D.host.E) • u) f = f := by
  have hΛ : ∀ x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplOH S T (incA D (w : D.host.E) • x) (incA D (w : D.host.E) • y)) = 1 :=
    fun x hx y hy => char_symplOH_smul hψ hS hT hw hx hy
  have h2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      2 • u ∈ fixGroup ψ _ _ hΛ := by
    intro u hu
    refine mem_fixGroup.2 ⟨nsmul_mem hu 2, fun f hf => ?_⟩
    have e : incA D (w : D.host.E) • (2 • u) = 2 • (incA D (w : D.host.E) • u) := by
      rw [two_nsmul, two_nsmul, smul_add]
    rw [e]
    exact hf.1 _ (smul_mem_latO' w hu)
  have hh : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u → u ∈ fixGroup ψ _ _ hΛ := by
    intro e he u hu hh
    refine mem_fixGroup.2 ⟨hu, fun f hf => hf.2 e he _ (smul_mem_latO' w hu) fun i j => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hh i j]
  exact (mem_fixGroup.1 (GlobalTheory.LatVac.le_of_two_of_half _ h2 hh hu)).2 f hf

theorem hRat_smul_smul (a b : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (a • M) (b • N) = a * star b * GlobalTheory.LatVac.hRat S T M N := by
  simp only [GlobalTheory.LatVac.hRat, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem finRat_eq (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T M = GlobalTheory.LatVac.finTens 1 M := by
  ext i j; rfl

theorem algebraMap_mul_pair (c : D.host.F) (β : Af D.host.F) :
    algebraMap D.host.F (AF D.host.F) c * pairA D.host.F 0 β =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) c * β) :=
  Prod.ext (mul_zero _) rfl

end GlobalTheory.LatVacSign

open GlobalTheory.LatVacSign in

theorem GlobalTheory.LatVacSign.heisO_finRat_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf v hv
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hst : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.host.d : ℤ) + 1 = 8 * n :=
    ⟨((D.host.d : ℤ) + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  have hnE : (D.host.d : D.host.E) = 8 * n - 1 := by
    have := congrArg (Int.cast (R := D.host.E)) hn
    push_cast at this
    linear_combination this
  set w₀ : D.host.E := (1 + D.host.sqrtMinusD) / 2 with hw₀
  have hstw : star w₀ = 1 - w₀ := by
    rw [hw₀, star_div₀, star_add, star_one, hst, star_ofNat]
    ring
  have hnorm : w₀ * (1 - w₀) = 2 * n := by
    rw [hw₀]
    linear_combination (-1 / 4 : D.host.E) * hsq + (1 / 4 : D.host.E) * hnE
  have hint : IsIntegral ℤ w₀ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * n), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, eq_intCast]
    push_cast
    linear_combination (-1 : D.host.E) * hnorm
  let W : 𝓞 D.host.E := ⟨w₀, hint⟩
  let W' : 𝓞 D.host.E := 1 - W
  have hW : (W : D.host.E) = w₀ := rfl
  have hW' : (W' : D.host.E) = 1 - w₀ := by
    change algebraMap (𝓞 D.host.E) D.host.E (1 - W) = 1 - w₀
    rw [map_sub, map_one]
    rfl
  have nW : (W : D.host.E) * star (W : D.host.E) = 2 * n := by rw [hW, hstw, hnorm]
  have nW' : (W' : D.host.E) * star (W' : D.host.E) = 2 * n := by
    rw [hW', star_sub, star_one, hstw, sub_sub_cancel, mul_comm, hnorm]
  set u := GlobalTheory.VacUnique.finRat S T (-v) with hu_def
  have h1 := heisO_smul_fix hψ hS hT W nW hv f hf
  have h2 := heisO_smul_fix hψ hS hT W' nW' hv f hf
  have hsum : incA D (W : D.host.E) • u + incA D (W' : D.host.E) • u = u := by
    rw [← add_smul, ← map_add, hW, hW', add_sub_cancel, map_one, one_smul]
  have key := GlobalTheory.LatVac.heisO_heisO ψ (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) f
  rw [h2, h1, hsum] at key

  set z : D.host.E := D.host.xi0 * w₀ ^ 2 * GlobalTheory.LatVac.hRat S T v v with hz
  have hpair : symplO S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E z)) := by
    rw [hu_def, finRat_eq, incA_smul_finTens, incA_smul_finTens, GlobalTheory.LatVac.symplO_finTens, one_mul, one_mul]
    congr 3
    rw [hz, ← neg_one_smul D.host.E v, smul_smul, smul_smul, hRat_smul_smul, hW, hW', star_mul', star_sub,
      star_one, hstw, star_neg, star_one]
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Algebra.trace ℚ D.host.E z = k := by
    have := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (smul_mem_latO' W hv) (smul_mem_latO' W' hv)
    rw [hpair] at this
    exact (GlobalTheory.LatVac.char_rat hψ z).1 this
  have hsign : ψ (symplOH S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u)) = (-1 : ℂ) ^ k := by
    rw [symplOH, hpair, algebraMap_mul_pair, ← map_mul, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ]
    have e : Algebra.trace ℚ D.host.F (1 / 2 * Algebra.trace D.host.F D.host.E z) = (1 / 2 : ℚ) * k := by
      have h12 : (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) := by simp
      rw [h12, ← Algebra.smul_def, map_smul, Algebra.trace_trace, hk, smul_eq_mul]
    rw [e, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hsign] at key
  refine ⟨k, hk.symm, ?_⟩
  have hsq1 : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_zpow]; norm_num
  calc heisO ψ S T u f = (((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k) • heisO ψ S T u f := by rw [hsq1, one_smul]
    _ = (-1 : ℂ) ^ k • f := by rw [mul_smul, ← key]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightInRangePlusSubmoduleStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  first | exact @GlobalTheory.SteepMult.hw_lift_orth | exact GlobalTheory.SteepMult.hw_lift_orth | (intros; apply GlobalTheory.SteepMult.hw_lift_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightModuleUnitaryFormStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_module_unitary_form : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∃ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsUnitary actW B := by
  first | exact @GlobalTheory.UnitaryTrick.exists_isUnitary | exact GlobalTheory.UnitaryTrick.exists_isUnitary | (intros; apply GlobalTheory.UnitaryTrick.exists_isUnitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightTensorRootShiftStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_tensor_root_shift : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  first | exact @GlobalTheory.SteepMult.hw_tensor_one | exact GlobalTheory.SteepMult.hw_tensor_one | (intros; apply GlobalTheory.SteepMult.hw_tensor_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractionsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  first | (exact @GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (exact GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (intros; apply GlobalTheory.homotopyInv_quot_iInf_ker_retractions  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacesIffGoodPrimesFixedByConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  first | exact @GlobalTheory.InertPlaces.inert_places_iff | exact GlobalTheory.InertPlaces.inert_places_iff | (intros; apply GlobalTheory.InertPlaces.inert_places_iff <;> assumption)
end

