import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem specPhi_coord {Z N C : Type} [CommRing Z] [AddCommGroup N] [Module Z N] [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (u : N →ₗ[Z] N)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (u (b j)) i)) (t : N) :
    (fun i => φ (b.repr (u t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  funext i
  conv_lhs => rw [← b.sum_repr t]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_mul, Matrix.mulVec, dotProduct, hU]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem specPhi_coord_smul {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t) [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (a : O)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (a • b j) i)) (t : N) :
    (fun i => φ (b.repr (a • t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  have hlin : ∀ (x : Z) (s : N), a • (x • s) = x • (a • s) := by
    intro x s
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  let u : N →ₗ[Z] N :=
    { toFun := fun s => a • s
      map_add' := fun x y => smul_add a x y
      map_smul' := fun x s => hlin x s }
  exact specPhi_coord φ b u U hU t

theorem specPhi_generic {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (L : R → Matrix (Fin d) (Fin d) C) (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (co : ↥T.L.T →+ (Fin d → C))
    (hco : ∀ (a : O) t, co (a • t) = (L (algebraMap O R a)).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (t : ↥T.L.T), Φ (r ⊗ₜ[O] t) = (L r).mulVec (co t)) ∧
      ∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z) := by
  let f : R →+ ↥T.L.T →+ (Fin d → C) :=
    { toFun := fun r =>
        { toFun := fun t => (L r).mulVec (co t)
          map_zero' := by simp
          map_add' := fun x y => by simp [Matrix.mulVec_add] }
      map_zero' := by ext t : 1; simp [hL0]
      map_add' := fun x y => by ext t : 1; simp [hLa, Matrix.add_mulVec] }
  have hf : ∀ (a : O) (r : R) (t : ↥T.L.T), f (a • r) t = f r (a • t) := by
    intro a r t
    show (L (a • r)).mulVec (co t) = (L r).mulVec (co (a • t))
    rw [Algebra.smul_def, mul_comm, hLm, hco, Matrix.mulVec_mulVec]
  refine ⟨TensorProduct.liftAddHom f hf, fun r t => rfl, fun r z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show (L (r * x)).mulVec (co t) = (L r).mulVec ((L x).mulVec (co t))
    rw [hLm, Matrix.mulVec_mulVec]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, Matrix.mulVec_add]

theorem specPhi_equiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (u : R →ₐ[O] R) (g : G) (U : Matrix (Fin d) (Fin d) C)
    (σ : C ≃+* C)
    (h : ∀ (r : R) (t : ↥T.L.T), Φ (u r ⊗ₜ[O] T.actT g t) =
      U.mulVec (fun i => σ (Φ (r ⊗ₜ[O] t) i))) (z : TW R T) :
    Φ (TWact u T g z) = U.mulVec (fun i => σ (Φ z i)) := by
  unfold TWact
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero U).symm
  | tmul r t => exact h r t
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
    congr 1
    funext i
    simp [map_add]

theorem specPhi_norm {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (S : AddSubmonoid C)
    (h : ∀ (r : R) (t : ↥T.L.T) i, Φ (r ⊗ₜ[O] t) i ∈ S) (z : TW R T) (i : Fin d) :
    Φ z i ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => exact h r t i
  | add x y hx hy => simpa using S.add_mem hx hy

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000 in

theorem specPhi_co (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (h : IsMat K LL T M A)
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act) :
    ∃ co : ↥T.L.T →+ (Fin d → PadicComplex l), (∀ t i, co t i ∈ (PadicComplexInt l).toSubring) ∧
      (∀ (g : ↥(GK K)) t i, act (g : GQ l) (co t i) = co t i) ∧
      (∀ (a : ↥(OL LL)) (t : ↥T.L.T), co (a • t) = (A a).mulVec (co t)) ∧
      (∀ (g : ↥(GK K)) (t : ↥T.L.T), co (T.actT g t) = (M (g : GQ l)).mulVec (co t)) ∧
      ∀ j, ∃ t, co t = Pi.single j 1 := by
  obtain ⟨b, hM, hA⟩ := h
  letI := zlMod LL T
  let φ : ℤ_[l] →+* PadicComplex l :=
    (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  let co : ↥T.L.T →+ (Fin d → PadicComplex l) :=
    { toFun := fun t i => zC (b.repr t i)
      map_zero' := by funext i; simp [zC]
      map_add' := fun x y => by funext i; simp [zC] }
  refine ⟨co, fun t i => ?_, fun g t i => act_zC hact _ _, fun a t => ?_, fun g t => ?_,
    fun j => ⟨b j, ?_⟩⟩
  · exact (mem_OC _).2 ((norm_zC _).le.trans (PadicInt.norm_le_one _))
  · have hs : ∀ (x : ℤ_[l]) (s : ↥T.L.T), x • s = algebraMap ℤ_[l] ↥(OL LL) x • s :=
      fun x s => rfl
    exact specPhi_coord_smul hs φ b a (A a) (fun i j => hA a i j) t
  · exact specPhi_coord φ b (actTZ LL T g) (M g) (fun i j => hM g i j) t
  · funext i
    show zC (b.repr (b j) i) = (Pi.single j (1 : PadicComplex l) : Fin d → PadicComplex l) i
    rw [b.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [zC]
    · simp [zC, hij]

theorem specPhi_abstract {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d f : ℕ}
    (S : Subring C) (A : O → Matrix (Fin d) (Fin d) C) (M : G → Matrix (Fin d) (Fin d) C)
    (σ : G → C ≃+* C) (u : G → R →ₐ[O] R) (o : Fin f → O) (κ : R → Fin f → C)
    (L : R → Matrix (Fin d) (Fin d) C) (hL : ∀ r, L r = ∑ k, κ r k • A (o k))
    (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (hal : ∀ a, L (algebraMap O R a) = A a) (hone : A 1 = 1)
    (hκS : ∀ r k, κ r k ∈ S) (hκ : ∀ g r k, κ (u g r) k = σ g (κ r k))
    (co : ↥T.L.T →+ (Fin d → C)) (hS : ∀ t i, co t i ∈ S) (hσ : ∀ g t i, σ g (co t i) = co t i)
    (hcoA : ∀ (a : O) t, co (a • t) = (A a).mulVec (co t))
    (hcoM : ∀ g t, co (T.actT g t) = (M g).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z)) ∧
      (∀ z i, Φ z i ∈ S) ∧
      (∀ g z, Φ (TWact (u g) T g z) = (M g).mulVec (fun i => σ g (Φ z i))) ∧
      ∀ t : ↥T.L.T, Φ ((1 : R) ⊗ₜ[O] t) = co t := by
  obtain ⟨Φ, hΦt, hΦs⟩ := specPhi_generic T L hL0 hLa hLm co (fun a t => by rw [hcoA, hal])
  have hLco : ∀ r t, (L r).mulVec (co t) = ∑ k, κ r k • co (o k • t) := by
    intro r t
    rw [hL, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, hcoA]
  refine ⟨Φ, hΦs, fun z i => specPhi_norm T Φ S.toAddSubmonoid (fun r t i => ?_) z i,
    fun g z => specPhi_equiv T Φ (u g) g (M g) (σ g) (fun r t => ?_) z, fun t => ?_⟩
  · show _ ∈ S
    rw [hΦt, hLco, Finset.sum_apply]
    refine S.sum_mem fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact S.mul_mem (hκS r k) (hS _ i)
  · rw [hΦt, hΦt, hLco, hLco]
    have h1 : ∀ k, co (o k • T.actT g t) = (M g).mulVec (co (o k • t)) := fun k => by
      rw [← map_smul (T.actT g) (o k) t, hcoM]
    have h2 : (fun i => σ g ((∑ k, κ r k • co (o k • t)) i)) =
        ∑ k, κ (u g r) k • co (o k • t) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, ← hκ]
    rw [h2, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1, Matrix.mulVec_smul]
  · have h1 : L 1 = 1 := by rw [← map_one (algebraMap O R), hal, hone]
    rw [hΦt, h1, Matrix.one_mulVec]

set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_thR_alg (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) :
    thR LL θ (algebraMap ↥(OL LL) (RA LL) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
  rw [Algebra.TensorProduct.algebraMap_apply, thR_tmul, map_one]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_specPhi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  intro l _ P AI K LL T d f n M A o θ hM hθ
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨co, hS, hσ, hcoA, hcoM, hsingle⟩ := specPhi_co K LL T M A hM hact
  have hmul := lam_mul_of_isMat l K LL T d f M A o hM
  have hL : ∀ r : RA LL, lam o A (thR LL θ r) = ∑ k, kap o (thR LL θ r) k • A (o k) :=
    fun r => rfl
  have hL0 : lam o A (thR LL θ 0) = 0 := by rw [map_zero, lamMul_lam_zero]
  have hLa : ∀ x y : RA LL, lam o A (thR LL θ (x + y)) =
      lam o A (thR LL θ x) + lam o A (thR LL θ y) := fun x y => by
    rw [map_add, lamMul_lam_add]
  have hLm : ∀ x y : RA LL, lam o A (thR LL θ (x * y)) =
      lam o A (thR LL θ x) * lam o A (thR LL θ y) := fun x y => by
    rw [map_mul, hmul.2.2.2]
  have hal : ∀ a : ↥(OL LL), lam o A (thR LL θ (algebraMap ↥(OL LL) (RA LL) a)) = A a :=
    fun a => by rw [specPhi_thR_alg, hmul.1]; simp
  have hκS : ∀ (r : RA LL) (k : Fin f), kap o (thR LL θ r) k ∈ (PadicComplexInt l).toSubring :=
    fun r k => (mem_OC _).2 (norm_kap_le o _ k)
  have hκ : ∀ (g : ↥(GK K)) (r : RA LL) (k : Fin f),
      kap o (thR LL θ (gRA AI LL (g : GQ l) r)) k = AI.actC (g : GQ l) (kap o (thR LL θ r) k) :=
    fun g r k => kap_thR_gRA AI o hθ _ r k
  have keyA := specPhi_abstract (R := RA LL) T (PadicComplexInt l).toSubring
    A (fun g => M (g : GQ l)) (fun g => AI.actC (g : GQ l)) (fun g => gRA AI LL (g : GQ l)) o
    (fun r k => kap o (thR LL θ r) k) (fun r => lam o A (thR LL θ r)) hL hL0 hLa hLm hal
    hmul.2.1 hκS hκ co hS hσ hcoA hcoM
  obtain ⟨Φ, hΦs, hΦS, hΦg, hΦ1⟩ := keyA
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact hΦs
  · intro z i
    exact (mem_OC _).1 (hΦS z i)
  · intro g z
    convert hΦg g z using 3
  · intro j
    obtain ⟨t, ht⟩ := hsingle j
    exact ⟨t, (hΦ1 t).trans ht⟩

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem exists_fundamental_cocycle_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧
      ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]),
        Continuous (fun g => (χ g : ℤ_[l])) ∧
        (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧
        (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧
        ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
          ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  intro l _ P K
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  refine ⟨Φ.symm.surjective.compactSpace hΦ1, χZ.comp Φ.toMonoidHom, _, hχc.comp hΦ2,
    fun g => ?_, fun r => (hc r).transport Φ hΦ2 hΦ1, fun r hr => ?_⟩
  · have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    exact h1
  · have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hfin := (GlobalTheory.T.finite_H1_H2_local hT l K.1 K.2 r (ZMod (l ^ r))
      (ReciprocityTheory.Gal.charRep (redChar χZ r)) hr
      (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
    obtain ⟨e⟩ := (GlobalTheory.contCohomology_transport_mulEquiv (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1)
      ↥(GK K) (ZMod (l ^ r)) Φ hΦ2 hΦ1 (ReciprocityTheory.Gal.charRep (redChar χZ r))
      (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
        (χZ.comp Φ.toMonoidHom))) (fun g m => rfl)).1
    exact Finite.of_equiv _ e

end GlobalTheory.TateTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwist
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

theorem isSSRep_rank_one {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* GL (Fin 1) k) : IsSSRep χ := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have h : ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k).mulVec v =
      ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k) 0 0 • v := by
    funext j
    fin_cases j
    simp [Matrix.mulVec, dotProduct]
  rw [h]
  exact W'.smul_mem _ hv

theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist

open GlobalTheory.HalfTwist in

theorem GlobalTheory.HalfTwist.exists_galRep_halfTwist : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (e : ℤ), D.naut.csd π → (∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ z ∈ D.naut.infG π τ, ∃ k : ℤ, z + (e : ℂ) / 2 = (k : ℂ)) → ∃ ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((e : ℝ) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG π ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (e : ℂ) / 2))) := by
  intro D htie hadm i a ha π e hcsd hinf
  obtain ⟨hLP, hAut, hGal⟩ := htie
  obtain ⟨hG1, -, hG3⟩ := hadm i
  have hoff : ∀ {b : ℕ} (ρ : GE D.nd →* GL (Fin b) (Qbar (D.nd.l i))) (f : ∀ w, D.naut.LP w),
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = f w) →
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.wdOf i ρ w = f w) → ∀ w, D.naut.wdOf i ρ w = f w := by
    intro b ρ f h1 h2 w
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · exact h2 w hw
    · exact h1 w hw
  rcases Int.even_or_odd (e + (a : ℤ) - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    have hkC : (e : ℂ) + (a : ℂ) - 1 = (k : ℂ) + (k : ℂ) := by exact_mod_cast hk
    have hkR : (e : ℝ) + (a : ℝ) - 1 = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hralg : D.naut.ralg π := by
      rw [D.naut.ralg_def]
      intro τ
      refine ⟨(hinf τ).1, fun z hz => ?_⟩
      obtain ⟨m, hm⟩ := (hinf τ).2 z hz
      exact ⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩
    obtain ⟨ρ₀, hc0, hss0, hoff0, hon0⟩ := hG1 a ha π hcsd hralg
    have hinf0 : ∀ τ, D.naut.infG (D.naut.tw D.naut.etaT D.naut.etaTinv) τ = {0} := by
      intro τ
      obtain ⟨h, h1, h2, -⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw _ _ τ (-h) h2, h1, Multiset.map_singleton, add_neg_cancel]
    obtain ⟨ρχ, hcχ, hoffχ, honχ⟩ := hG3 (D.naut.tw D.naut.etaT D.naut.etaTinv) (k : ℝ) (fun τ z hz => by
      rw [hinf0, Multiset.mem_singleton] at hz
      exact ⟨k, by rw [hz]; push_cast; ring⟩)
    obtain ⟨ρ', h1, h2, h3, h4⟩ := GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ
      (fun w => D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
      (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw D.naut.etaT D.naut.etaTinv) w) (k : ℝ))
      (fun τ => (D.naut.infG π τ).map (fun z => -z + ((a : ℂ) - 1) / 2))
      (fun _ => -(k : ℂ))
      ⟨hc0, hss0, hoff ρ₀ _ (fun w hw => (hoff0 w hw).1) (fun w hw => (hon0 w hw).2.2),
        fun w hw => ⟨(hon0 w hw).1, fun τ hτ => by rw [(hon0 w hw).2.1 τ hτ, D.naut.jumpsInf_def i π τ hralg]⟩⟩
      ⟨hcχ, isSSRep_rank_one ρχ, hoff ρχ _ hoffχ (fun w hw => (honχ w hw).2.1),
        fun w hw => ⟨(honχ w hw).1, fun τ hτ => by
          rw [(honχ w hw).2.2 τ hτ, hinf0, Multiset.map_singleton, zero_add]
          push_cast
          rfl⟩⟩
    refine ⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩
    · rw [h3 w]
      have hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1 := by
        rw [(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]
      rw [D.naut.locG_tw, eta_char,
        (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
          (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) (k : ℝ) hU hU).2.2.1,
        (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
          (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) (k : ℝ) hU hU).2.2.2.2.1,
        D.naut.lpTw_add]
      congr 1
      linear_combination (-1 / 2 : ℝ) * hkR
    · rw [(h4 w hw).2 τ hτ, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      linear_combination hkC / 2
  ·
    have hkC : (e : ℂ) + (a : ℂ) - 1 = 2 * (k : ℂ) + 1 := by exact_mod_cast hk
    have hkR : (e : ℝ) + (a : ℝ) - 1 = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have hcsd' : D.naut.csd (D.naut.tw π D.naut.etaT) := D.naut.csd_tw π D.naut.etaT hAut.1.1 hcsd
    have hinfπ : ∀ τ, D.naut.infG (D.naut.tw π D.naut.etaT) τ =
        (D.naut.infG π τ).map (· + (D.naut.infG D.naut.etaT τ).sum) := by
      intro τ
      obtain ⟨h, h1, -, -⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw π D.naut.etaT τ h h1, h1, Multiset.sum_singleton]
    have hralg : D.naut.ralg (D.naut.tw π D.naut.etaT) := by
      rw [D.naut.ralg_def]
      intro τ
      obtain ⟨h, h1, -, hh⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw π D.naut.etaT τ h h1]
      refine ⟨(hinf τ).1.map (add_left_injective h), fun z' hz' => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
      obtain ⟨m, hm⟩ := (hinf τ).2 z hz
      rcases hh with rfl | rfl
      · exact ⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩
      · exact ⟨m - k - 1, by push_cast; linear_combination hm - hkC / 2⟩
    obtain ⟨ρ₀, hc0, hss0, hoff0, hon0⟩ := hG1 a ha _ hcsd' hralg
    obtain ⟨ρχ, hcχ, hoffχ, honχ⟩ := hG3 D.naut.etaTinv ((k : ℝ) + 1 / 2) (fun τ z hz => by
      obtain ⟨h, -, h2, hh⟩ := eta_inf D hAut τ
      rw [h2, Multiset.mem_singleton] at hz
      rcases hh with rfl | rfl
      · exact ⟨k, by rw [hz]; push_cast; ring⟩
      · exact ⟨k + 1, by rw [hz]; push_cast; ring⟩)
    obtain ⟨ρ', h1, h2, h3, h4⟩ := GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ
      (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaT) w) ((1 - (a : ℝ)) / 2))
      (fun w => D.naut.lpTw (D.naut.locG D.naut.etaTinv w) ((k : ℝ) + 1 / 2))
      (fun τ => (D.naut.infG (D.naut.tw π D.naut.etaT) τ).map (fun z => -z + ((a : ℂ) - 1) / 2))
      (fun τ => -((D.naut.infG D.naut.etaTinv τ).sum + (((k : ℝ) + 1 / 2 : ℝ) : ℂ)))
      ⟨hc0, hss0, hoff ρ₀ _ (fun w hw => (hoff0 w hw).1) (fun w hw => (hon0 w hw).2.2),
        fun w hw => ⟨(hon0 w hw).1, fun τ hτ => by rw [(hon0 w hw).2.1 τ hτ, D.naut.jumpsInf_def i _ τ hralg]⟩⟩
      ⟨hcχ, isSSRep_rank_one ρχ, hoff ρχ _ hoffχ (fun w hw => (honχ w hw).2.1),
        fun w hw => ⟨(honχ w hw).1, fun τ hτ => by
          rw [(honχ w hw).2.2 τ hτ]
          obtain ⟨h, -, h2, -⟩ := eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)
          rw [h2, Multiset.map_singleton, Multiset.sum_singleton]⟩⟩
    refine ⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩
    · rw [h3 w]
      have hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1 := by
        rw [(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]
      have hη : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
      have hη' : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
      rw [D.naut.locG_tw,
        (hLP w (D.naut.lpTw (D.naut.lpChar (D.naut.locG π w) (D.naut.locG D.naut.etaT w)) ((1 - (a : ℝ)) / 2))
          (D.naut.locG π w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w)
          ((k : ℝ) + 1 / 2) hη' hη').2.2.1,
        (hLP w (D.naut.lpChar (D.naut.locG π w) (D.naut.locG D.naut.etaT w))
          (D.naut.locG π w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w)
          ((1 - (a : ℝ)) / 2) hη' hη').2.1,
        (hLP w (D.naut.locG π w) (D.naut.locG π w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w)
          0 hη hη').2.2.2.1,
        eta_char,
        (hLP w (D.naut.locG π w) (D.naut.locG π w) (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) 0 hU hU).2.2.2.2.1,
        D.naut.lpTw_add]
      congr 1
      linear_combination (-1 / 2 : ℝ) * hkR
    · rw [(h4 w hw).2 τ hτ, hinfπ, Multiset.map_map, Multiset.map_map]
      obtain ⟨h, h1', h2', -⟩ := eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)
      rw [h1', h2', Multiset.sum_singleton, Multiset.sum_singleton]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      push_cast
      linear_combination hkC / 2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBijection
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_letter_bijection {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) :
    ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)),
      Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  obtain ⟨-, -, -, hSb, hSσ, -⟩ := S.hyp.1
  have hWb := (S.W H).emb_bij
  have hWσ := (S.W H).emb_σ
  have key : ∀ j, (S.W H).emb ((Equiv.ofBijective _ hWb).symm j) = j :=
    Equiv.ofBijective_apply_symm_apply _ hWb
  refine ⟨fun i => (Equiv.ofBijective _ hWb).symm (S.emb i),
    (Equiv.ofBijective _ hWb).symm.bijective.comp hSb, fun i => key _, fun i => hWb.1 ?_⟩
  calc (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb (i - 1)))
      = S.emb (i - 1) := key _
    _ = (S.emb (i - 1 + 1)).comp (P.PD S.K).σ := (hSσ _).symm
    _ = ((S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i))).comp (P.PD S.K).σ := by
        rw [sub_add_cancel, key]
    _ = (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1) := by
        rw [← hWσ ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1), sub_add_cancel]

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemTameDescentClassEqOfPowMemStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  first | exact @GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq | exact GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq | (intros; apply GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOneStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  first | exact @GlobalTheory.NormChar.exists_prime_norm_char_ne_one | exact GlobalTheory.NormChar.exists_prime_norm_char_ne_one | (intros; apply GlobalTheory.NormChar.exists_prime_norm_char_ne_one <;> assumption)
end

