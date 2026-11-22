import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem L_proj (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hW : ∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) (hg : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := GlobalTheory.T.fock_invariant_subspace_equivariant_projection p q r s W hW hg

theorem L_grad (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := GlobalTheory.T.homogeneous_component_in_range_embedding P Q R h k G n

theorem L_inj (P Q R : ℕ) (h : P ≤ R) (k : ℕ) : Function.Injective (embR P Q R h k) := GlobalTheory.T.injective_rank_embedding P Q R h k

theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G
  · exact GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G
  · exact GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G
  · exact GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G

theorem L_actS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (i j : Ix P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab i j) f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' i j G)) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fischer_pairing_adjoint_upper_block P Q S h k' a a' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_upper P Q S h k' a b' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_lower P Q S h k' a' b G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_lower_block P Q S h k' b b' G f

theorem L_tensor (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ) (hb : b ≠ 0)
    (hinv : ∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) :
    GlobalTheory.RealLift.HasForm P Q R S x := GlobalTheory.T.nonzero_equivariant_pairing_has_form P Q R S x b hb hinv

theorem L_detS (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := detS_ne_zero P Q S h

theorem op_sum' (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (i j : Ix P Q) :
    opR P Q R k i j + opS P Q S k' i j = (if i = j then x else 0) • (1 : Module.End ℂ (Mdl P Q)) := by
  have hk' : ((S + k' : ℕ) : ℂ) = ((R + k : ℕ) : ℂ) := by rw [hk]
  have hk2 : (k' : ℂ) = R + k - S := by
    have := congrArg (fun n : ℕ => (n : ℂ)) hk; push_cast at this; linear_combination this
  rcases i with a | b <;> rcases j with a' | b'
  · simp only [opR, opS, Sum.inl.injEq]
    split_ifs with hh
    · rw [hx]; module
    · simp
  · simp [opR, opS]
  · simp only [opR, opS, hk', reduceCtorEq, if_false, zero_smul]
    abel
  · simp only [opR, opS, Sum.inr.injEq]
    split_ifs with hh
    · rw [hx, hk2]; module
    · simp

theorem act_sum (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (Z : Mat P Q) (G : Mdl P Q) :
    actR P Q R k Z G + actS P Q S k' Z G = (x * Z.trace) • G := by
  have h : actR P Q R k Z + actS P Q S k' Z = (x * Z.trace) • (1 : Module.End ℂ (Mdl P Q)) := by
    rw [actR_apply, actS_apply, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← smul_add, op_sum' P Q R S k k' x hk hx, smul_smul, mul_ite, mul_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_smul]
    congr 1
    simp [Matrix.trace, Finset.mul_sum, mul_comm, mul_add]
  rw [← LinearMap.add_apply, h]; simp

theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

theorem actS_full (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (Z : Mat P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S Z f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (actS P Q S k' Z G)) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actS, actS_apply, smul_eq_mul]

theorem formEx : GlobalTheory.RealLift.FormEx := by
  intro P Q R S x k k' hP hQ _ _ hk hk'
  have hkk : S + k' = R + k := by
    have h1 : ((S + k' : ℕ) : ℚ) = ((R + k : ℕ) : ℚ) := by
      push_cast; rw [← hk, ← hk']; unfold cPair; ring
    exact_mod_cast h1
  have hx : (x : ℂ) = k + (R : ℂ) / 2 - (S : ℂ) / 2 := by
    have : x = k + (R : ℚ) / 2 - (S : ℚ) / 2 := by rw [← hk]; unfold cPair; ring
    rw [this]; push_cast; ring
  set e := embR P Q R hP k
  have hinj := L_inj P Q R hP k
  obtain ⟨π, hπW, hπid, hπeq⟩ := L_proj P Q R 0 (LinearMap.range e)
    (by rintro Z _ ⟨G, rfl⟩; exact ⟨_, (actR_full P Q R hP k Z G).symm⟩)
    (by rintro _ ⟨G, rfl⟩ n; exact L_grad P Q R hP k G n)
  let eq := LinearEquiv.ofInjective e hinj
  let κ : Pol P Q R 0 →ₗ[ℂ] Mdl P Q := eq.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ π hπW
  have hκ : ∀ f, e (κ f) = π f := by
    intro f
    have := eq.apply_symm_apply ⟨π f, hπW f⟩
    simpa [eq, κ] using congrArg Subtype.val this
  have hκeq : ∀ Z f, κ (fockAct1 P Q R 0 Z f) = actR P Q R k Z (κ f) := by
    intro Z f; apply hinj
    rw [hκ, hπeq, ← hκ, actR_full]
  have hκ1 : κ (e 1) = 1 := by
    apply hinj; rw [hκ, hπid _ ⟨1, rfl⟩]
  let b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ :=
    GlobalTheory.DefLift.BilFischer.pair.flip ∘ₗ (embS P Q S hQ k') ∘ₗ κ
  have hb : ∀ f g, b f g = GlobalTheory.DefLift.BilFischer.pair g (embS P Q S hQ k' (κ f)) := fun _ _ => rfl
  apply L_tensor P Q R S x b
  · intro h0
    have hne : embS P Q S hQ k' 1 ≠ 0 := by
      simp only [embS, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one, LinearMap.mulRight_apply, one_mul]
      exact pow_ne_zero _ (L_detS P Q S hQ)
    apply hne
    apply GlobalTheory.DefLift.BilFischer.pair_nondeg
    intro g
    have := congrArg (fun t => t (e 1) g) h0
    simpa [hb, hκ1] using this
  · intro Z f g
    rw [hb, hb, hb, hκeq, actS_full, ← map_add, ← map_add, act_sum P Q R S k k' x hkk hx, map_smul, map_smul,
      smul_eq_mul]

end GlobalTheory.CharPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullSumRegroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dif_pos h]⟩

def summand {G : HTGroup p} (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (c : ConjClasses (grp G β)) : ℂ :=
  if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β (Classical.choose (ConjClasses.exists_rep c) : grp G β) z) then wt (minpoly G.F ((((Classical.choose (ConjClasses.exists_rep c) : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {(Classical.choose (ConjClasses.exists_rep c) : grp G β)}).subtype) ((toP1 G β).comp (Subgroup.centralizer {(Classical.choose (ConjClasses.exists_rep c) : grp G β)}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx (Classical.choose (ConjClasses.exists_rep c) : grp G β)) (toP1 G β (Classical.choose (ConjClasses.exists_rep c) : grp G β)) f f' else 0

end GlobalTheory.LKCx.Regroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfPartsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_expansion_of_parts : EllTrace → EllipticPart → RealStable → GeomExpansion := by
  first | exact @GlobalTheory.TrMult.geomExpansion_of_parts | exact GlobalTheory.TrMult.geomExpansion_of_parts | (intros; apply GlobalTheory.TrMult.geomExpansion_of_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

variable {D : D7}

def SiegelWeilFockAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

def GlobalFormAnisoAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalFormAniso (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAnisoAt A L

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

def trivPar (a : ℕ) : LFun.Fam D.host.E := LFun.segFam (fun _ => 1) a

end GlobalTheory.BottomRallis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroupStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.levi σ J X Y S := by
  first | exact @GlobalTheory.TieStd.leviFlag_le_levi | exact GlobalTheory.TieStd.leviFlag_le_levi | (intros; apply GlobalTheory.TieStd.leviFlag_le_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def growth : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (g * infGL E a y)‖ ≤ C * height y ^ N}
  zero_mem' g := ⟨0, 0, fun y => by simp⟩
  add_mem' {f f'} h h' g := by
    obtain ⟨C, N, hC⟩ := h g
    obtain ⟨C', N', hC'⟩ := h' g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have h1 := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have q1 : 0 ≤ height y ^ N := le_trans zero_le_one (one_le_pow₀ h1)
    have q2 : 0 ≤ height y ^ N' := le_trans zero_le_one (one_le_pow₀ h1)
    calc ‖(f + f') (g * infGL E a y)‖ ≤ ‖f (g * infGL E a y)‖ + ‖f' (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (hC y) (hC' y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) q1).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') q2).trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring
  smul_mem' c f h g := by
    obtain ⟨C, N, hC⟩ := h g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)

variable (E a) in

def tame : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ l : List (Lie E a), ((l.map (lie E a)).prod ψ).1 ∈ growth E a}
  zero_mem' l := by simp
  add_mem' {ψ ψ'} h h' l := by
    rw [map_add, Submodule.coe_add]
    exact add_mem (h l) (h' l)
  smul_mem' c ψ h l := by
    rw [map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ c (h l)

theorem growth_of_tame {ψ : Sm E a} (h : ψ ∈ tame E a) : ψ.1 ∈ growth E a := by
  simpa using h []

theorem lie_mem_tame (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ tame E a) : lie E a X ψ ∈ tame E a := by
  intro l
  have e : (l.map (lie E a)).prod (lie E a X ψ) = ((l ++ [X]).map (lie E a)).prod ψ := by
    simp [List.map_append, List.prod_append, Module.End.mul_apply]
  rw [e]
  exact h _

def dens (X : Lie E a) (α : Lie E a → ℂ) (x : Lie E a) : ℂ :=
  -(fderiv ℝ α x (lmul X x) + (LinearMap.trace ℝ (Lie E a) (lmul X).toLinearMap : ℂ) * α x)

def KInv (α : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a),
    α (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = α x

def maps (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a))
    (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) : Submodule ℂ (W →ₗ[ℂ] Sm E a) where
  carrier := {T | (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
    ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w}
  zero_mem' := ⟨fun k w => by simp, fun w => ⟨by simp, fun _ _ => rfl, fun k _ => by simp⟩⟩
  add_mem' {T T'} h h' := ⟨fun k w => by simp [h.1 k w, h'.1 k w], fun w =>
    ⟨by simpa using add_mem (h.2 w).1 (h'.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g, (h'.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk, (h'.2 w).2.2 k hk]⟩⟩
  smul_mem' c T h := ⟨fun k w => by simp [h.1 k w], fun w =>
    ⟨by simpa using Submodule.smul_mem _ c (h.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk]⟩⟩

theorem isTest_dens (X : Lie E a) {α : Lie E a → ℂ} (h : GlobalTheory.CuspQuot.IsTest (invSet E a) α) :
    GlobalTheory.CuspQuot.IsTest (invSet E a) (dens X α) := by
  have hs : Function.support (dens X α) ⊆ tsupport α := by
    intro x hx
    by_contra hn
    apply hx
    have h1 : α x = 0 := image_eq_zero_of_notMem_tsupport hn
    have h2 : fderiv ℝ α x = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [dens, h1, h2]
  have ht : tsupport (dens X α) ⊆ tsupport α := closure_minimal hs (isClosed_tsupport α)
  refine ⟨?_, h.2.1.mono' hs, ht.trans h.2.2⟩
  refine (((h.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmul X).contDiff).add
    (contDiff_const.mul h.1)).neg

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HadamardIneqComplexCombinationsBasisStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hadamard_ineq_complex_combinations_basis : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) (d : ℕ) (b : Module.Basis (Fin d) F V) (σ : F →+* ℂ) (P : Matrix (Fin d) (Fin d) ℂ), 0 < (nm.gram σ b).det.re ∧ ‖P.det‖ * Real.sqrt (nm.gram σ b).det.re ≤ ∏ k, cnrm nm σ (fun i => P i k) b := by
  first | exact @GlobalTheory.HSShort.hadamard_basis_comb | exact GlobalTheory.HSShort.hadamard_basis_comb | (intros; apply GlobalTheory.HSShort.hadamard_basis_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre
section
open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilExGen

theorem exists_isWeil : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om :=
  fun h => h.weilRepresentationExists

end GlobalTheory.WeilExGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RallisBottom

open GlobalTheory.Core.Rk.IP

variable {D : D7}

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

end GlobalTheory.RallisBottom

end
end

