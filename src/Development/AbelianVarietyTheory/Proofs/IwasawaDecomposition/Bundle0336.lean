import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  first | exact @GlobalTheory.Mem.LiftGrow.growth_pair | exact GlobalTheory.Mem.LiftGrow.growth_pair | (intros; apply GlobalTheory.Mem.LiftGrow.growth_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem pureTensorL_rename {ι κ X : Type} {A : κ → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f)) {f : X → ℂ} (hf : P f)
    (e : ι → κ) (Q : MvPolynomial ι ℂ) :
    pureTensorL (fun i => A (e i)) f Q = pureTensorL A f (MvPolynomial.rename e Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.rename_monomial, Ker.FockAlg.pure_monomial, Ker.FockAlg.pure_monomial]
    congr 1
    unfold opPow
    rw [← List.foldr_map (f := e) (g := fun i g => A i g)]
    refine Ker.FockAlg.foldr_perm hA hc hf ?_
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
      Finsupp.toMultiset_map]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (π : Equiv.Perm (Fin m))
    (a : Fin m) (k : Fin n) : unitMap B (Z.submatrix id π) (π.symm a) k = unitMap B Z a k := by
  unfold unitMap
  congr 1
  ext i j
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

theorem fvec_perm {D : D7} {S T : HSp D} (C : Ker.Ctx S T) (Z : Fam T) (π : Equiv.Perm (Fin T.rank))
    (hB : C.IsB fun ρ => (Z ρ).submatrix id π) {f : WO S T → ℂ} (hf : C.IsTh f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB fun ρ => (Z ρ).submatrix id π) (fun _ => 1) Z f Q =
      C.fvec (fun ρ => (Z ρ).submatrix id π) f (MvPolynomial.rename (fun v => (v.1, π.symm v.2.1, v.2.2)) Q) := by
  have h := pureTensorL_rename (P := C.IsTh)
    (A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB (fun ρ => (Z ρ).submatrix id π) τ)) (fun _ => 1)
      (fun ρ => (Z ρ).submatrix id π))
    (fun _ _ h => Ker.FockAlg.aPlus_th C _ _ _ h)
    (fun i j _ h => Ker.FockAlg.aPlus_comm C i.1 _ hB j.1 _ h) hf
    (fun v : FVar D T.rank S.rank => (v.1, π.symm v.2.1, v.2.2)) Q
  refine Eq.trans ?_ h
  unfold pureTensorO
  congr 2
  funext v
  simp only [aPlusAll, unitMap_perm]

theorem zak_laws : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → (∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → (∃ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → (∀ f', Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f' → f' = f) ∧ (∀ φ', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f → φ' = φ) ∧ (∀ a : ℂ, Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • φ) (a • f)) ∧ (∀ φ' f', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f' → Zak ψ θ hr eT bas idx (frOf hr eT Z) (φ + φ') (f + f')) ∧ (∀ y : Matrix (Fin S.rank) (Fin r) D.host.E, Zak ψ θ hr eT bas idx (frOf hr eT Z) (heisG X bas (-y) φ) (heisO ψ S T (finR S hr y) f)) ∧ (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) ∧ ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), fv ψ θ S T X.p0 Z f Q 0 = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) → ∃ φ : TF S.rank g, GlobalTheory.SW.IsSB φ ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  have hq0 : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, hheis, hZZ⟩ :=
    GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0) hq0
  obtain ⟨hB, hrest⟩ := hZZ Z
  obtain ⟨hsB, hzak, hthP⟩ := hrest hZ
  have hB := hB.1 hZ
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set B : C.Bas := fun ρ => (Z ρ).submatrix id π with hBdef
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have key : ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f,
      Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f ↔ f = C.Th (C.xB B) φ := by
    intro φ hφ f
    rw [← hzak]
    exact ⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).2 f, fun h => h ▸ (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1⟩
  refine ⟨fun φ hφ => ⟨⟨_, (key φ hφ _).2 rfl⟩, fun f hf => ?_⟩, fun f hf hF => ?_⟩
  · have hth : C.IsTh f := hf.1
    obtain rfl := (key φ hφ f).1 hf
    obtain ⟨l1, l2, l3, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx φ hφ
    obtain ⟨f1, f2⟩ := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ
    refine ⟨fun f' hf' => (key φ hφ f').1 hf', fun φ' hφ' h => ?_, fun a => ?_, fun φ' f' hφ' h => ?_,
      fun y => ?_, fun ρ => ?_, fun q0 hq Q => ?_⟩
    · exact ((l1 φ' hφ').2 ((key φ' hφ' _).1 h)).symm
    · exact (key _ ((GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a) _).2 (l2 a).symm
    · rw [(key φ' hφ' _).1 h]
      exact (key _ (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1 _).2 (l1 φ' hφ').1.symm
    · refine (key _ ((heisG_laws _ r X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (-y) φ hφ).1 _).2 ?_
      rw [← hheis]
      exact l3 _
    · rw [← hsB]
      exact f1 ρ
    · obtain rfl : q0 = r - X.p0 := by omega
      rw [← hthP, fv, ← hsB]
      exact (congrFun (fvec_perm C Z π hB hth Q) 0).trans (f2 _)
  · obtain ⟨φ, ⟨hφ, h⟩, -⟩ := (Ker.th_bij_fock D S T C B hB).2 f hf (fun ρ => by rw [hsB]; exact hF ρ)
    exact ⟨φ, hφ, (key φ hφ f).2 h⟩

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjointCompositeLiftRowMemSpanGoodRationalForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.UpKeep3

section Abstract

theorem mem_span_of_op {K : Type} [Field K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V] [Module K V] [AddCommGroup H]
    [Module ℂ H] (j : V →ₛₗ[σ] H) {ι : Type} (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (C : H →ₗ[ℂ] H) (φ : V → V) (hC : ∀ z, C (j z) = j (φ z)) (v : H) :
    C v ∈ Submodule.span ℂ (Set.range fun z => j (φ z)) := by
  have hv : v ∈ Submodule.span ℂ (Set.range fun k => j (b k)) := hsp ▸ Submodule.mem_top
  have h : Submodule.span ℂ (Set.range fun k => j (b k)) ≤ (Submodule.span ℂ (Set.range fun z => j (φ z))).comap C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show C (j (b k)) ∈ Submodule.span ℂ (Set.range fun z => j (φ z))
    rw [hC]
    exact Submodule.subset_span ⟨b k, rfl⟩
  exact h hv

theorem sum_apply_j {K : Type} [Field K] {σ : K →+* ℂ} {G V H : Type} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [AddCommGroup H] [Module ℂ H] (j : V →ₛₗ[σ] H) (r : Representation K G V) (ρ : Representation ℂ G H)
    (hj : ∀ g z, j (r g z) = ρ g (j z)) (a : G → K) (z : V) :
    (∑ g, σ (a g) • ρ g) (j z) = j ((∑ g, a g • r g) z) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]

theorem adjoint_comm {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (π : H →ₗ[ℂ] H)
    (hπ : ∀ x, ‖π x‖ = ‖x‖) (ρ : E →ₗ[ℂ] E) (hρ : ∀ y, ‖ρ y‖ = ‖y‖) (h : ∀ y, Θ (ρ y) = π (Θ y)) (x : H) :
    ρ (LinearMap.adjoint Θ x) = LinearMap.adjoint Θ (π x) := by
  have hinj : Function.Injective ρ := (injective_iff_map_eq_zero ρ).2 fun y hy => by
    rw [← norm_eq_zero, ← hρ, hy, norm_zero]
  refine ext_inner_left ℂ fun v => ?_
  obtain ⟨y, rfl⟩ := LinearMap.surjective_of_injective hinj v
  rw [(LinearMap.norm_map_iff_inner_map_map ρ).1 hρ, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, h,
    (LinearMap.norm_map_iff_inner_map_map π).1 hπ]

theorem mem_span_untwist {s : Bool} {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : ι → E) (z : E)
    (h : Tw.mk s z ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) : z ∈ Submodule.span ℂ (Set.range f) := by
  have hle : Submodule.span ℂ (Set.range fun i => Tw.mk s (f i)) ≤ Tw.sub s (Submodule.span ℂ (Set.range f)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (R := ℂ) (M := E) ⟨i, rfl⟩
  exact hle h

theorem adjoint_mem_span {K G V E H ι : Type} [Field K] {σ : K →+* ℂ} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (j : V →ₛₗ[σ] E) (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (r : Representation K G V)
    (π : Representation ℂ G H) (hπ : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (Θ : E →ₗ[ℂ] H)
    (hρ : ∃ ρ : Representation ℂ G E, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧ ∀ g y, Θ (ρ g y) = π g (Θ y))
    (a l : G → K) (u : H) (ha : ∑ g, σ (a g) • π g u = u) (hl : ∑ g, σ (l g) • π g u = u) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range fun z => j ((∑ g, a g • r g) ((∑ g, l g • r g) z))) := by
  obtain ⟨ρ, hj, hn, hΘ⟩ := hρ
  have e1 : ∀ g, ρ g (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ (π g u) := fun g =>
    adjoint_comm Θ (π g) ((LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπ g)) (ρ g) (hn g) (hΘ g) u
  have fix : ∀ c : G → K, ∑ g, σ (c g) • π g u = u →
      (∑ g, σ (c g) • ρ g) (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u := fun c hc => by
    conv_rhs => rw [← hc]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, e1, map_sum, map_smul]
  have h := mem_span_of_op j b hsp ((∑ g, σ (a g) • ρ g) ∘ₗ (∑ g, σ (l g) • ρ g))
    (fun z => (∑ g, a g • r g) ((∑ g, l g • r g) z))
    (fun z => by rw [LinearMap.comp_apply, sum_apply_j j r ρ hj, sum_apply_j j r ρ hj]) (LinearMap.adjoint Θ u)
  rwa [LinearMap.comp_apply, fix l hl, fix a ha] at h

theorem untwist_adjoint {s : Bool} {E H ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (u : H) (f : ι → E) (f' : κ → E)
    (hf : ∀ i, ∃ k, f i = f' k)
    (h : LinearMap.adjoint (Tw.map s Θ) (Tw.mk s u) ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range f') := by
  rw [Tw.adjoint_map] at h
  refine Submodule.span_mono ?_ (mem_span_untwist (s := s) f _ h)
  rintro _ ⟨i, rfl⟩
  exact (hf i).elim fun k hk => ⟨k, hk.symm⟩

theorem exists_lvl_coord {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (z : S.Forms) :
    ∃ x, S.gaOp r (lvlIdem P ψ) z = S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) := by
  obtain ⟨w, rfl⟩ := S.basis.equivFun.symm.surjective z
  have h : S.gaMat r (lvlIdem P ψ) *ᵥ w ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K _ _).2]
    exact ⟨w, rfl⟩
  obtain ⟨x, hx⟩ := h
  exact ⟨x, (GlobalTheory.Mem.LiftForms.gaOp_coord S r _ w).trans (congrArg _ hx.symm)⟩

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

theorem exists_rowForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ} (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (t : T) (z : (A.MtildeCSD t).Forms) :
    ∃ x, (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (lvlIdem P ψ) z) =
      rowForm A P ψ t ((rE D A P ψ t).mulVec x) :=
  (exists_lvl_coord (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ z).elim fun x hx =>
    ⟨x, (congrArg ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X)) hx).trans (GoodProj.rowForm_rE ok P ψ t x).symm⟩

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_lvl_fix (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (u : (R.toCx3 F).EE) (hu : u ∈ (R.toCx3 F).EEl true) :
    ∑ g, A3.A.fam.v0.embedding ((lvlIdem F.P1 F.ψ1).coeff g) • R.gEx F g u = u := by
  rw [(GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC).2] at hu
  refine GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) F.P1 F.ψ1 fun h => ?_
  have := (Submodule.mem_iInf _).1 hu h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem adjoint_mem_tw (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (u : (R.toCx3 F).EE)
    (hu : u ∈ (R.toCx3 F).EEl true) :
    LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u ∈ Submodule.span ℂ (Set.range fun z => (R.toCx3 F).jR A3.A.fam.μ0
      ((∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g)
        ((∑ g, (lvlIdem F.P1 F.ψ1).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g) z))) :=
  adjoint_mem_span (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (E := (R.toCx3 F).FC A3.A.fam.μ0) ((R.toCx3 F).jR A3.A.fam.μ0)
    (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (RealDat3.kFormR_of (F := F) hC.base.models A3.A.fam.μ0).2
    (A3.A.fam.R A3.A.fam.μ0).r (R.gEx F) hH.prim.gUnit.1 ((R.toCx3 F).Θ A3.A.fam.μ0)
    (GlobalTheory.RowsPosRed.exists_rho R F (s := 1) hH.ok hC.base.models hH.prim.gEquiv)
    (fun g => (idemOf A3.A.X).coeff g) (fun g => (lvlIdem F.P1 F.ψ1).coeff g) u
    (GlobalTheory.RowsPosRed.sum_idem_gEx R F (GlobalTheory.CoreOfWeak.core_of_weak R F hC hH.aux.ex).1 u) (sum_lvl_fix R F hC u hu)

theorem adjoint_mem_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (w : R.HE.H)
    (hw : R.HE.e w ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) :
    LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (Set.range fun x =>
      R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) :=
  untwist_adjoint (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.μ0) w
    (fun z => R.jX A3.A.μ0 ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (idemOf A3.A.X)
      ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (lvlIdem F.P1 F.ψ1) z))) _
    (fun z => (exists_rowForm hH.ok.ok2 F.P1 F.ψ1 A3.A.μ0 z).elim fun x hx => ⟨x, congrArg (R.jX A3.A.μ0) hx⟩)
    (adjoint_mem_tw R F hC hH (Tw.mk (twAt D.what₂.embLL A3.A.v0) w) hw)

end GlobalTheory.UpKeep3

namespace GlobalTheory.UpKeep3

theorem adjoint_mem_span_rowForm : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH uE hread y
  have hrow : R.HE.e (uE y) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := by
    have h1 := (Y.Ish.jE y).2
    rw [hread y] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    have e : m = R.HE.e (uE y) := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective hm'
    rw [← e]
    exact hm
  exact adjoint_mem_of_row R F hP.char hH (uE y) hrow

end GlobalTheory.UpKeep3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitone
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AlgWtHW
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField Finset

section
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sle_mulVec {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ} (hM : ∀ A, M * Φ A = Φ A * M)
    (lam : Fin n → ℤ) {x : ι → ℂ} (hx : x ∈ Sle Φ lam) : M *ᵥ x ∈ Sle Φ lam := by
  have h : Sle Φ lam ≤ (Sle Φ lam).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨ν, hν, hw⟩
    refine Submodule.subset_span ⟨ν, hν, fun D hD => ?_⟩
    show Φ D *ᵥ (M *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw D hD, Matrix.mulVec_smul]
    rfl
  exact h hx

theorem filter_succ (i : Fin n) : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) =
    insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem not_mem_filter_self (i : Fin n) : i ∉ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
  simp

theorem domLE_antisymm {μ lam : Fin n → ℤ} (h1 : DomLE μ lam) (h2 : DomLE lam μ) : μ = lam := by
  have hs : ∀ k : ℕ, ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), lam i := fun k => le_antisymm (h1.2 k) (h2.2 k)
  funext i
  have h := hs ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i), hs i] at h
  linarith

theorem le_of_domLE_swap {lam : Fin n → ℤ} {i j : Fin n} (hij : i < j)
    (h : DomLE (lam ∘ Equiv.swap i j) lam) : lam j ≤ lam i := by
  have h1 := h.2 ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i)] at h1
  have h2 : ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), (lam ∘ Equiv.swap i j) l =
      ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), lam l := by
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl
    have hli : l ≠ i := fun e => by rw [e] at hl; omega
    have hlj : l ≠ j := fun e => by rw [e] at hl; rw [Fin.lt_def] at hij; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [h2] at h1
  simp only [Function.comp, Equiv.swap_apply_left] at h1
  linarith

end

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem algWeight_space_nontrivial (a : AlgWt L n) : Nontrivial a.W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := a.irr
  exact bot_ne_top (α := Subrepresentation a.ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem beig_of_hwAt {a : AlgWt L n} {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
      (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (v : ι → ℂ),
      Agrees a b P ∧ IsBEig (fun B => evM P (evPt τ B)) v lam := by
  obtain ⟨ι, i1, i2, b, P, hP, v, hv, hB⟩ := h
  exact ⟨ι, i1, i2, b, P, v, hP, hv, hB⟩

theorem domLE_of_agrees {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) {v : ι → ℂ} {lam μ : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P (evPt τ B)) v lam) (hμ : IsWt (fun B => evM P (evPt τ B)) μ) :
    DomLE μ lam := by
  obtain ⟨w, hw0, hw⟩ := hμ
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  refine GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy n ι _ hR μ lam w hw hw0 ?_
  have hspan := GlobalTheory.T.algebraicWeight_span_translates_factor_commutant L n a ι b P hP τ v hv.1 w
  refine (Submodule.span_le.2 ?_) hspan
  rintro x ⟨B, M, hM, rfl⟩
  have e : evM P (evPt τ B) *ᵥ (M *ᵥ v) = M *ᵥ (evM P (evPt τ B) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  rw [e]
  exact sle_mulVec hM lam (GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector n ι _ hR v lam hv B)

theorem isWt_of_beig {ι : Type} [Fintype ι] {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {v : ι → ℂ} {lam : Fin n → ℤ}
    (h : IsBEig Φ v lam) : IsWt Φ lam :=
  ⟨v, h.1, fun D hD => h.2 D (fun i j hij => hD (ne_of_gt hij))⟩

theorem beig_transport {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {b' : Module.Basis ι' ℂ a.W} {P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) (hP' : Agrees a b' P') {v' : ι' → ℂ} {lam : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P' (evPt τ B)) v' lam) :
    IsBEig (fun B => evM P (evPt τ B)) (b.toMatrix b' *ᵥ v') lam := by
  have hC : b'.toMatrix b * b.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' b
  refine ⟨fun h0 => hv.1 ?_, fun B hB => ?_⟩
  · have := congrArg (fun x => b'.toMatrix b *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, hC] using this
  · show evM P (evPt τ B) *ᵥ (b.toMatrix b' *ᵥ v') = _
    rw [GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis L n a ι' b' P' ι b P hP' hP τ B, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hC,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have := hv.2 B hB
    simp only at this
    rw [this, Matrix.mulVec_smul]

theorem hw_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  intro L _ _ _ n a τ
  have hanti : ∀ lam, a.HWAt τ lam → Antitone lam := by
    intro lam h
    obtain ⟨ι, _, _, b, P, v, hP, hv⟩ := beig_of_hwAt h
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hlt
    · rw [e]
    · exact le_of_domLE_swap hlt (domLE_of_agrees hP hv
        (GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ) lam (isWt_of_beig hv) i j))
  refine ⟨?_, hanti⟩
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  haveI := algWeight_space_nontrivial a
  haveI := b.index_nonempty
  obtain ⟨v, lam, hv⟩ := GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ)
  refine ⟨lam, ⟨ι, inferInstance, inferInstance, b, P, hP, v, hv.1, hv.2⟩, fun lam' h' => ?_⟩
  obtain ⟨ι', _, _, b', P', v', hP', hv'⟩ := beig_of_hwAt h'
  have hv'' := beig_transport hP hP' hv'
  exact domLE_antisymm (domLE_of_agrees hP hv (isWt_of_beig hv'')) (domLE_of_agrees hP hv'' (isWt_of_beig hv))

end

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicSideTransfer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem twist_settings_unread : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (N : TwNew D), (∃ A' : SideA N.toD7 (N.cf cf) jE, A'.row = N.row A.row ∧ (∀ lam, A'.pl.ι lam = A.pl.ι lam) ∧ (∀ w a, A'.wdT.e w a = A.wdT.e w a) ∧ (∀ j h1 h2 π, A'.au.cls j h1 h2 π = A.au.cls j h1 h2 π) ∧ ∀ hL, (Nonempty (CGTrue hL D A.wdT) → Nonempty (CGTrue hL N.toD7 A'.wdT)) ∧ (AUTrue hL D A.wdT A.au → AUTrue hL N.toD7 A'.wdT A'.au)) ∧ (∀ M tup Q, MtInput D M tup Q → MtInput N.toD7 (N.mt M) tup Q) ∧ (BlocksUnique D → BlocksUnique N.toD7) := by
  intro D cf jE A N
  let A' : SideA N.toD7 (N.cf cf) jE :=
    { bare := A.bare
      wdT := A.wdT
      lab := A.lab
      chr := { A.chr with }
      row := N.row A.row
      pl := { A.pl with }
      iota := A.iota
      wd := { A.wd with }
      grp := { A.grp with }
      par := { A.par with }
      au := { A.au with }
      chiT := A.chiT }
  refine ⟨⟨A', rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun hL => ⟨fun ⟨h⟩ => ⟨{ h with }⟩, fun h => h⟩⟩,
    fun M tup Q h => { h with }, fun h => h⟩

end GlobalTheory.HeightCounting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevNegFinSumBlockDiagonalMatrix
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem det_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).det = a.det * b.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem neg_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : -(blockSum a b) = blockSum (-a) (-b) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem one_sub_smul_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) :
    (1 - (Polynomial.X : Polynomial R) • (blockSum a b).map Polynomial.C) =
      blockSum (1 - (Polynomial.X : Polynomial R) • a.map Polynomial.C)
        (1 - (Polynomial.X : Polynomial R) • b.map Polynomial.C) := by
  rw [blockSum_map]
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [show (1 : Matrix (Fin (M + N)) (Fin (M + N)) (Polynomial R)) i j =
      (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) (Polynomial R)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) by
    simp [Matrix.one_apply]]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [Matrix.one_apply]

theorem charpolyRev_neg_blockSum : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  intro R _ M N a b
  rw [neg_blockSum, Matrix.charpolyRev, Matrix.charpolyRev, Matrix.charpolyRev, one_sub_smul_blockSum, det_blockSum]

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRankStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_kFinite_finiteRank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  first | exact @GlobalTheory.TypeSum.kAvg_finite_rank | exact GlobalTheory.TypeSum.kAvg_finite_rank | (intros; apply GlobalTheory.TypeSum.kAvg_finite_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionEmbeddingCompatibleClosuresStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_embedding_compatible_closures : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  first | exact @GlobalTheory.normGroup_adjoin_eq_norm_range_completion | exact GlobalTheory.normGroup_adjoin_eq_norm_range_completion | (intros; apply GlobalTheory.normGroup_adjoin_eq_norm_range_completion <;> assumption)
end

