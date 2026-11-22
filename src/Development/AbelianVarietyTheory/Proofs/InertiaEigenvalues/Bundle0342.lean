import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open Classical in

theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeAdjointLeOfComp
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin

theorem prj_mul_goodOp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} (Z : Submodule K B.S.Forms) {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold Formalism.L2.DIV.goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

theorem range_adjoint_le_of_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) (e : V →ₗ[ℂ] V)
    (hs : e.IsSymmetric) (h : θ ∘ₗ e = θ) : LinearMap.range (LinearMap.adjoint θ) ≤ LinearMap.range e := by
  rintro y ⟨x, rfl⟩
  refine ⟨LinearMap.adjoint θ x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  rw [hs (LinearMap.adjoint θ x) z, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun h z
  rw [LinearMap.comp_apply] at this
  rw [this]

theorem thetaCut_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (S0 : IndefData (A.side P ψ Zs)) (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → (∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = jW i ((S0.θ i t).mulVec ((lPrj D A P ψ Zs i t).mulVec x))) → ThetaCut D (tup t) ((i : ℕ) + 1) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i t hF hθ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : lPrj D A P ψ Zs i t * lE D A P ψ i t = lPrj D A P ψ Zs i t := prj_mul_goodOp (Zs.Zl i t) hB
  refine range_adjoint_le_of_comp _ _ (D.what₂.eMt_sa _ _) ?_
  refine LinearMap.ext_on_range hF.span fun k => ?_
  rw [LinearMap.comp_apply, hF.op_eq]
  refine (hθ _).trans (Eq.trans ?_ (hθ _).symm)
  rw [Matrix.mulVec_mulVec (Pi.single k 1), hP]

end GlobalTheory.EtaJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducible_of_stable_rational_rowSubspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  first | exact @GlobalTheory.PMon.splits_of_stable_rat_subspace | exact GlobalTheory.PMon.splits_of_stable_rat_subspace | (intros; apply GlobalTheory.PMon.splits_of_stable_rat_subspace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relaxedResidualSelmer_mem_unrelaxed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  first | exact @GlobalTheory.ResUnr.unrelax | exact GlobalTheory.ResUnr.unrelax | (intros; apply GlobalTheory.ResUnr.unrelax <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentsOfComputes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.Growth

section Chg

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (h : ∀ g m, rho g m = rho' g m)

theorem mk_eq_mk_iff (z w : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = Submodule.Quotient.mk w ↔
    ∃ m, ∀ g, z.1 g - w.1 g = rho g m - m := by
  rw [Submodule.Quotient.eq]
  exact mem_coboundaries1 rho _

def chgZ (z : Z1 rho) : Z1 rho' := ⟨z.1, z.2.1, fun g k => by rw [← h]; exact z.2.2 g k⟩

def chg : H1 rho → H1 rho' :=
  Quotient.map' (chgZ rho rho' h) fun z w hzw => by
    obtain ⟨m, hm⟩ := (mk_eq_mk_iff rho z w).1 (Quotient.sound' hzw)
    exact Quotient.exact' ((mk_eq_mk_iff rho' _ _).2 ⟨m, fun g => by rw [← h]; exact hm g⟩)

theorem chg_mk (z : Z1 rho) : chg rho rho' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (chgZ rho rho' h z) := rfl

theorem chg_zero : chg rho rho' h 0 = 0 := rfl

theorem chg_add (x y : H1 rho) : chg rho rho' h (x + y) = chg rho rho' h x + chg rho rho' h y := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  induction y using Submodule.Quotient.induction_on with
  | H w => rfl

theorem chg_smul (a : R) (a' : R') (ha : ∀ m : M, a • m = a' • m) (x : H1 rho) :
    chg rho rho' h (a • x) = a' • chg rho rho' h x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, chg_mk, chg_mk, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => ha _))

theorem chg_mem_span (hs : ∀ a : R, ∃ a' : R', ∀ m : M, a • m = a' • m) {S : Set (H1 rho)} {T : Submodule R' (H1 rho')}
    (hS : ∀ x ∈ S, chg rho rho' h x ∈ T) {x : H1 rho} (hx : x ∈ Submodule.span R S) : chg rho rho' h x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [chg_zero]; exact T.zero_mem
  | add x y _ _ hx hy => rw [chg_add]; exact T.add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨a', ha⟩ := hs a
    rw [chg_smul _ _ _ a a' ha]
    exact T.smul_mem a' hx

theorem chg_chg (x : H1 rho) : chg rho' rho (fun g m => (h g m).symm) (chg rho rho' h x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem res_chg {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (chg rho rho' h x) =
      chg (rho.comp phi) (rho'.comp phi) (fun g m => h (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem chg_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) : chg rho rho' h x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_chg rho rho' h J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (chg_zero _ _ _))

end Chg

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw)

section Sel

variable {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ']
  [Algebra (X.O0 i) Λ'] (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ)
  {B : Type} [AddCommGroup B] [Module Λ B] [Module Λ' B] [TopologicalSpace B] [DiscreteTopology B]
  (h : ∀ g m, repOn ρ κ B g m = repOn ρ κ' B g m) (hs : ∀ a : Λ, ∃ a' : Λ', ∀ b : B, a • b = a' • b)
  (ho : ∀ (y : X.O0 i) (b : B), algebraMap (X.O0 i) Λ y • b = algebraMap (X.O0 i) Λ' y • b)

include hs ho

theorem chg_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) :
    chg _ ((repOn ρ κ' B).comp (DecV N v).subtype) (fun g m => h g.1 m) x ∈ bkOn bkP i ρ κ' B v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · refine chg_mem_span _ _ _ (fun a => (hs a).imp fun a' ha m => funext fun c => ha (m c)) ?_ hx
    rintro x ⟨z, c, y, b, hc, hy, hz, rfl⟩
    exact Submodule.subset_span ⟨chgZ _ _ (fun g m => h g.1 m) z, c, y, b, hc, hy,
      fun g a => (hz g a).trans (ho _ _), rfl⟩
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx]
    exact chg_zero _ _ _

theorem chg_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : chg _ (repOn ρ κ' B) h x ∈ selOn bkP i ρ κ' B Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_chg (repOn ρ κ B) (repOn ρ κ' B) h (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact chg_mem_bkOn bkP i ρ κ κ' h hs ho v _ hv
  · exact Submodule.mem_top
  · exact chg_ur _ _ _ _ _ hv

end Sel

def Represents {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {R : Type} [CommRing R] [Algebra (X.O0 i) R] (κ : GE N →* Rˣ)
    (Q : Finset (PlE D.host)) {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ E : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      (Fin a → B) → H1 (repOn ρ κ B),
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B),
      matAct Ψ u = 0 → E B u ∈ selOn bkP i ρ κ B Q) ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B),
      matAct Ψ u = 0 → matAct Ψ u' = 0 → E B u = E B u' → u = u') ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      ∀ y ∈ selOn bkP i ρ κ B Q, ∃ u, matAct Ψ u = 0 ∧ E B u = y) ∧
    ∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B),
      matAct Ψ u = 0 → E B' (fun c => f (u c)) = h1Map ρ κ f (E B u)

variable {bkP i}

theorem represents_of_computes {s : X.Sig i} {M : ℕ} {ι : Type} {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {Q : Finset (PlE D.host)} {a : ℕ} {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)} (hΦ : Computes bkP i s M d Q Φ)
    {R : Type} [CommRing R] [Algebra (X.O0 i) R] (p : abelian₂ X i M ι →ₐ[X.O0 i] R) (hp : Function.Surjective p)
    (κ : GE N →* Rˣ) (hκ : ∀ g, p (delInv i M d g : (abelian₂ X i M ι)ˣ) = κ g) (n : ℕ) (hn : ((X.l i ^ n : ℕ) : R) = 0) :
    Represents bkP i (Tgl i s) κ Q (Φ.map p) := by
  classical
  obtain ⟨e, he⟩ := hΦ
  have tor : ∀ (B : Type) [AddCommGroup B] [Module R B], ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun B _ _ b =>
    ⟨n, by rw [← Nat.cast_smul_eq_nsmul R, hn, zero_smul]⟩
  let inst : ∀ (B : Type) [AddCommGroup B] [Module R B], Module (abelian₂ X i M ι) B := fun B _ _ =>
    Module.compHom B p.toRingHom
  have hsm : ∀ (B : Type) [AddCommGroup B] [Module R B] (x : abelian₂ X i M ι) (b : B), x • b = p x • b := fun _ _ _ _ _ => rfl
  have hk : ∀ (B : Type) [AddCommGroup B] [Module R B] (u : Fin a → B), matAct (Φ.map p) u = matAct Φ u :=
    fun _ _ _ _ => rfl
  have ho : ∀ (B : Type) [AddCommGroup B] [Module R B] (y : X.O0 i) (b : B),
      algebraMap (X.O0 i) (abelian₂ X i M ι) y • b = algebraMap (X.O0 i) R y • b := fun B _ _ y b => by
    rw [hsm, AlgHom.commutes]
  have hr : ∀ (B : Type) [AddCommGroup B] [Module R B] g m,
      repOn (Tgl i s) (delInv i M d) B g m = repOn (Tgl i s) κ B g m := fun B _ _ g m => by
    funext c
    change (delInv i M d g : abelian₂ X i M ι) • ∑ j, algebraMap (X.O0 i) (abelian₂ X i M ι) _ • m j =
      (κ g : R) • ∑ j, algebraMap (X.O0 i) R _ • m j
    rw [hsm, hκ]
    simp only [ho]
  refine ⟨fun B _ _ _ _ u => if h : matAct Φ u = 0 then chg _ _ (hr B) (e B (tor B) ⟨u, h⟩).1 else 0,
    fun B _ _ _ _ u hu => ?_, fun B _ _ _ _ u u' hu hu' huu => ?_, fun B _ _ _ _ y hy => ?_,
    fun B B' _ _ _ _ _ _ _ _ f u hu => ?_⟩
  · rw [hk] at hu
    simp only [dif_pos hu]
    exact chg_mem_selOn bkP i _ _ _ (hr B) (fun x => ⟨p x, hsm B x⟩) (ho B) Q _ (e B (tor B) ⟨u, hu⟩).2
  · rw [hk] at hu hu'
    simp only [dif_pos hu, dif_pos hu'] at huu
    have h1 := congrArg (chg _ _ fun g m => (hr B g m).symm) huu
    rw [chg_chg, chg_chg] at h1
    exact congrArg Subtype.val ((e B (tor B)).injective (Subtype.ext h1))
  · have h1 := chg_mem_selOn bkP i _ _ _ (fun g m => (hr B g m).symm)
      (fun x => by obtain ⟨x', rfl⟩ := hp x; exact ⟨x', fun b => (hsm B x' b).symm⟩) (fun y b => (ho B y b).symm) Q y hy
    obtain ⟨u, hu⟩ := (e B (tor B)).surjective ⟨_, h1⟩
    have hu0 : matAct Φ u.1 = 0 := u.2
    refine ⟨u.1, hu0, ?_⟩
    simp only [dif_pos hu0]
    rw [show (⟨u.1, hu0⟩ : LinearMap.ker (matAct (M := B) Φ)) = u from rfl, hu]
    exact chg_chg _ _ _ y
  · rw [hk] at hu
    let f' : B →ₗ[abelian₂ X i M ι] B' := ⟨f.toAddHom, fun x b => f.map_smul (p x) b⟩
    have hu' : matAct Φ (fun c => f (u c)) = 0 := by
      show matAct Φ (fun c => f' (u c)) = 0
      funext c
      have := congrArg f' (congrFun hu c)
      simpa [matAct, map_sum] using this
    simp only [dif_pos hu, dif_pos hu']
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B (tor B) ⟨u, hu⟩).1
    rw [he B B' (tor B) (tor B') f' ⟨u, hu⟩ ⟨_, hu'⟩ z (cocycles1MapOfEquivariant _ _ (f'.compLeft _) continuous_of_discreteTopology
      (repOn_map _ _ f') z) (fun _ => rfl) (fun _ _ => rfl) hz.symm, ← hz]
    rfl

end GlobalTheory.Growth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientFieldStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualSelmer_baseChange_coefficientField : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i k → Function.Surjective (algebraMap (X.O0 i) k) → IsRes i K → ∀ Q : Finset (PlE D.host), Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) → Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧ Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  first | exact @GlobalTheory.ResSel.BaseChange.selOn_baseChange | exact GlobalTheory.ResSel.BaseChange.selOn_baseChange | (intros; apply GlobalTheory.ResSel.BaseChange.selOn_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem colv_latC_and_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  intro l _ P r ω hω hdet n _ _ U x y A₀ hA W₀ hW hev
  have hit : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] b = (P.φB ^ m) b := fun m b => by rw [AlgHom.coe_pow]
  have hfix : ∀ (m : ℕ) i j, P.φB^[m] ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun m i j => Function.iterate_fixed (hA i j) m
  have hφcol : ∀ (m : ℕ) c i, P.φB^[m] (colv P ω A₀ c i) =
      ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c := by
    intro m c i
    rw [hit, colv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hit, ← hit, phi_iter_kur, hfix]
  have hsum : ∀ {R : Type} [CommRing R] (f : ↥(MaximalUnramifiedExtension l) →+* R) (X : Matrix (n × Fin r) (n × Fin r) R) (m : Fin r) (i : n) c,
      ∑ k, f (fr l m (ω k)) * X (i, k) c = ((resMat n ω).map f * X) (i, m) c := by
    intro R _ f X m i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [resMat_apply, apply_ite f, ite_mul]
  have hpU : (resMat n ω).map (kd P) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
      Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR) := by
    have e : (resMat n ω).map (kd P) = ((Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
        Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) : GL (n × Fin r) P.R.BdR) :
        Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
    rw [e, U0, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rfl
  have h0 : ∀ e f, P.ιB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) e f) =
      ((U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) e f := by
    intro e f; rw [← hev]; rfl
  have hcol : ∀ (m : Fin r) c i, ev P m (colv P ω A₀ c i) =
      ∑ j, (U m : Matrix n n P.R.BdR) i j * tz P (eps x y (m, j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c := by
    intro m c i
    rw [ev, hφcol, map_sum]
    simp only [map_mul, iota_kur, h0]
    rw [hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_mul, ite_mul, mul_assoc]
  refine ⟨fun c => ⟨fun i => ?_, fun m => ⟨fun j => (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c,
    fun j => hW.1 _ _, funext fun i => ?_⟩⟩, ?_⟩
  · rw [hφcol]; simp only [hω]; rfl
  · rw [hcol]; simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
  · haveI : Nontrivial P.R.BdR := ⟨⟨(P.PD (botExt l)).ι (P.PD (botExt l)).t, 0, fun h =>
      (P.PD (botExt l)).not_mem_filtration_two (by rw [h]; exact zero_mem _)⟩⟩
    haveI : Nontrivial P.R.B := ⟨⟨1, 0, fun h => one_ne_zero (by simpa using congrArg P.ιB h : (1 : P.R.BdR) = 0)⟩⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ c, g c • colv P ω A₀ c i = 0 := fun i => by
      have := congrFun hg i; simpa [Finset.sum_apply] using this
    have hYe : ∀ i (m : Fin r) c, Ymat P ω A₀ (i, m) c = P.φB^[m] (colv P ω A₀ c i) := by
      intro i m c
      rw [hφcol, hsum, Ymat]
    have hY : (Ymat P ω A₀).mulVec (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      funext ⟨i, m⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      calc ∑ c, Ymat P ω A₀ (i, m) c * algebraMap ℚ_[l] P.R.B (g c)
          = (P.φB ^ (m : ℕ)) (∑ c, g c • colv P ω A₀ c i) := by
            rw [map_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [hYe, hit, map_smul, Algebra.smul_def, mul_comm]
        _ = 0 := by rw [hg' i, map_zero]
    have hdetY : IsUnit (Ymat P ω A₀).det := by
      rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((isUnit_det_resMat n ω hdet).map _).mul ((Matrix.isUnit_iff_isUnit_det _).1 A₀.isUnit)
    have hv0 : (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      have := congrArg (Matrix.mulVec (Ymat P ω A₀)⁻¹) hY
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetY, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    intro c
    exact (algebraMap ℚ_[l] P.R.B).injective (by simpa using congrFun hv0 c)

end GlobalTheory.PMon.ResR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAndIsogenyInvariant
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem pow_smul_eq (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : LetA O n) ^ k • x = ((PD.p : ℕ) : O) ^ k • x := by
  rw [← map_natCast (algebraMap O (LetA O n)), ← map_pow, algebraMap_smul]

theorem sat_of (T : LocLat G Qp LL O)
    (hs : ∀ (m : ℕ) (x : W.DD T), ((PD.p : O) ^ m) • x ∈ W.N T → x ∈ W.N T) : wachSaturated W T := by
  rintro x ⟨k, hk⟩
  rw [pow_smul_eq] at hk
  exact hs k x hk

theorem isog_of {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L)
    (hi : Function.Bijective f.f → Function.Injective (W.map f) ∧
      (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
        (y ∈ W.N T → x ∈ W.N T')) ∧
      ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T') : p6V W f := by
  intro hf
  obtain ⟨hinj, ⟨c, hc⟩, -⟩ := hi hf
  refine ⟨fun x _ hx => hinj (hx.trans (map_zero _).symm), fun y hy => ?_⟩
  obtain ⟨x, hx, hxN⟩ := hc y
  exact ⟨c, x, hxN hy, hx.trans (pow_smul_eq W T c y).symm⟩

end Generic

set_option linter.unusedVariables false in

theorem saturated_and_isogeny_invariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; (∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → wachSaturated W T) ∧ ∀ (T' T : Lt K LL) (f : LatHom T'.L T.L), IsCrys ((D.loc l).PD K) T'.ρ → IsCrys ((D.loc l).PD K) T.ρ → p6V W f := by
  intro D HW F l _ K s LL h W E
  refine ⟨fun T hT => sat_of W T fun m x hx => sat_loc (HW l) K s LL h T hT m x hx,
    fun T' T f hT' hT => isog_of W f fun hf => isog_loc (HW l) K s LL h T' T f hT' hT hf⟩

end GlobalTheory.NL.Isog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtensionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmerObstruction_le_residualSelmer_simpleExtension : PoitouTateTotallyComplex → CohDimTwo → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → LocCount bkP i s κ → SelObs bkP i s κ Q := by
  first | exact @GlobalTheory.SelObstruction.selObs | exact GlobalTheory.SelObstruction.selObs | (intros; apply GlobalTheory.SelObstruction.selObs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponentsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_theorem_of_local_components : KernelRep → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → SelMaps bkP i s κ Q ∧ SelLeft bkP i s κ Q ∧ SelColim bkP i s κ Q ∧ SelObs bkP i s κ Q) → ThmS bkP := by
  first | exact @GlobalTheory.SelAssemble.thmS_of_selmer_functor | exact GlobalTheory.SelAssemble.thmS_of_selmer_functor | (intros; apply GlobalTheory.SelAssemble.thmS_of_selmer_functor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableLinearFormOnConstantsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearForm_semistable_extending_trace : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | exact GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | (intros; apply GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotentStatement
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
end

