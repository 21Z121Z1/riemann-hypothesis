import Mathlib
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaPhiBranchOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEdgesMemOfCoboundaryTwoCoeffsInIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck

noncomputable section

namespace GlobalTheory.BrCompare

def rE (K : Type) [Field K] (n m : ℕ) (i j : Fin n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  rowE K (n + 1) m i.castSucc j.castSucc

def rCap (K : Type) [Field K] (n m : ℕ) (u : ℤ) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  capDet (rE K n m) u

def lamN {n : ℕ} (lam : DomWeight (n + 1)) : Fin n → ℕ := fun i => lam.natW i.castSucc

def incl (K : Type) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  rename (Prod.map id Fin.castSucc)

def bfact {n : ℕ} (b : Fin n → ℕ) : ℕ := ∏ s, (b s).factorial

def coefOne (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ) (x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :
    MvPolynomial (Fin n × Fin n) K :=
  rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
    (Formalism.L2.Col.Br.coefLast (rfl : n + 1 = n + 1) (fun _ : Unit => b)
      (rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) x))

def zList {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) : List ℤ :=
  (List.ofFn fun i : Fin n => (((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet lam sg i).erase (sg.w i)).toList).map fun v =>
    v - lam.w (Fin.last n) - (i.val : ℤ)).flatten

section Basic

variable {K : Type} [Field K]

theorem fockB_symm {σ : Type} (f g : MvPolynomial σ K) : fockB f g = fockB g f :=
  @fockSHerm K _ starRingOfComm _ g f

theorem fockB_X_mul {σ : Type} (v : σ) (f g : MvPolynomial σ K) : fockB (X v * f) g = fockB f (pderiv v g) := by
  classical
  exact @fockL_X_pderiv K _ starRingOfComm σ _ v f g

theorem fockB_rowE {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) K) :
    fockB (rowE K r m a b f) g = fockB f (rowE K r m b a g) := by
  rw [rowE_apply, rowE_apply, ← fockBL_apply, ← fockBL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [fockBL_apply, fockBL_apply, fockB_X_mul, fockB_symm f, fockB_X_mul, fockB_symm]

theorem rE_rel (n m : ℕ) (i j k l : Fin n) :
    rE K n m i j * rE K n m k l - rE K n m k l * rE K n m i j =
      (if j = k then rE K n m i l else 0) - (if i = l then rE K n m k j else 0) := by
  have h := glRel_rowE K (n + 1) m i.castSucc j.castSucc k.castSucc l.castSucc
  simp only [Fin.castSucc_inj] at h
  simp only [rE, h, eq_comm (a := l)]

theorem end_two [CharZero K] {M : Type} [AddCommGroup M] [Module K M] (x : Module.End K M) (h : x + x = 0) : x = 0 := by
  rw [← two_smul K x] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

theorem rE_comm_rCap [CharZero K] (n m : ℕ) (u : ℤ) (k l : Fin n) : Commute (rE K n m k l) (rCap K n m u) :=
  capDet_central _ u (rE_rel n m) end_two k l

theorem rCap_comm [CharZero K] (n m : ℕ) (u v : ℤ) : Commute (rCap K n m u) (rCap K n m v) :=
  capDet_commute_of _ v _ fun i j => (rE_comm_rCap n m u i j).symm

theorem rowE_mem {r m : ℕ} {ν : Fin m → ℕ} (a b : Fin r) {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ dualWeyl K r m ν) : rowE K r m a b f ∈ dualWeyl K r m ν := by
  rw [(rowE_eq_rowDiv K r m a b f).1]
  exact rowDivStable K r m ν a b 1 f hf

theorem capDet_intertwine {M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M'] {n : ℕ}
    (E : Fin n → Fin n → Module.End K M) (E' : Fin n → Fin n → Module.End K M') (φ : M →ₗ[K] M')
    (h : ∀ i j x, E' i j (φ x) = φ (E i j x)) (u : ℤ) (x : M) : capDet E' u (φ x) = φ (capDet E u x) := by
  have h1 : ∀ (k a i : Fin n) x, bmF E' u k a i (φ x) = φ (bmF E u k a i x) := by
    intro k a i x
    unfold bmF
    split_ifs
    · simp only [LinearMap.sub_apply, Module.End.intCast_apply, h, map_sub, map_zsmul]
    · simp [h]
  have h2 : ∀ (l : List (Fin n)) (α β : Fin n → Fin n) x, (l.map fun k => bmF E' u k (α k) (β k)).prod (φ x) =
      φ ((l.map fun k => bmF E u k (α k) (β k)).prod x) := by
    intro l α β x
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, h1]
  simp only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, List.ofFn_eq_map, h2]

theorem capDet_mem {M : Type} [AddCommGroup M] [Module K M] {n : ℕ} (E : Fin n → Fin n → Module.End K M)
    (W : Submodule K M) (h : ∀ i j, ∀ x ∈ W, E i j x ∈ W) (u : ℤ) {x : M} (hx : x ∈ W) : capDet E u x ∈ W := by
  have := capDet_intertwine (fun i j => (E i j).restrict (h i j)) E W.subtype (fun _ _ _ => rfl) u ⟨x, hx⟩
  rw [show x = W.subtype ⟨x, hx⟩ from rfl, this]
  exact Subtype.property _

theorem rE_emb (n : ℕ) (i j : Fin n) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (emb K n f) = emb K n (rowE K n n i j f) := by
  unfold rE
  induction f using MvPolynomial.induction_on with
  | C a => simp [emb, rowE_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    rw [map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, bmF_emb_X, rowE_X, rowE_X]
    by_cases h : j = a <;> simp [h, bmF_emb_X]

theorem rE_zmon (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) : rE K n n i j (zmon K n b) = 0 := by
  unfold rE zmon
  refine Finset.prod_induction _ (fun P => rowE K (n + 1) n i.castSucc j.castSucc P = 0) ?_ ?_ ?_
  · intro a b ha hb
    rw [rowE_mul, ha, hb]; simp
  · exact rowE_C K _ _ _ _ 1
  · intro s _
    induction b s with
    | zero => exact rowE_C K _ _ _ _ 1
    | succ k ih => rw [pow_succ, rowE_mul, ih, rowE_X, if_neg (Fin.castSucc_lt_last j).ne]; simp

theorem rE_lead (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (zmon K n b * emb K n f) = zmon K n b * emb K n (rowE K n n i j f) := by
  have h1 := rE_zmon (K := K) n i j b
  have h2 := rE_emb n i j f
  unfold rE at *
  rw [rowE_mul, h1, h2, zero_mul, zero_add]

theorem rCap_lead (n : ℕ) (u : ℤ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rCap K n n u (zmon K n b * emb K n f) = zmon K n b * emb K n (capDet (fun i j => rowE K n n i j) u f) :=
  capDet_intertwine (fun i j => rowE K n n i j) (rE K n n)
    (LinearMap.mulLeft K (zmon K n b) ∘ₗ (emb K n).toLinearMap) (fun i j x => rE_lead n i j b x) u f

theorem rE_incl (n : ℕ) (i j : Fin n) (f : BP K n) :
    rE K n (n + 1) i j (incl K n f) = incl K n (rE K n n i j f) := by
  unfold rE
  induction f using MvPolynomial.induction_on with
  | C a => simp [incl, rowE_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    have hX : ∀ a s, incl K n (X (a, s)) = X (a, s.castSucc) := fun a s => rename_X _ _
    rw [map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, hX, rowE_X, rowE_X]
    by_cases h : j.castSucc = a <;> simp [h, hX]

theorem rCap_incl (n : ℕ) (u : ℤ) (f : BP K n) : rCap K n (n + 1) u (incl K n f) = incl K n (rCap K n n u f) :=
  capDet_intertwine (rE K n n) (rE K n (n + 1)) (incl K n).toLinearMap (rE_incl n) u f

theorem rowE_eq_deriv {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) K) :
    rowE K r m a b f = mkDerivation K (fun v : Fin r × Fin m =>
      if v.1 = b then (X (a, v.2) : MvPolynomial (Fin r × Fin m) K) else 0) f := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [rowE_C, derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    rw [rowE_mul, hp, Derivation.leibniz, mkDerivation_X, rowE_X]
    simp only [smul_eq_mul, eq_comm (a := b)]
    ring

theorem comp_comm_rE {B : Type} [AddCommMonoid B] [IsRightCancelAdd B] (n m : ℕ) (w : Fin (n + 1) × Fin m → B)
    (hw : ∀ (a a' : Fin n) s, w (a.castSucc, s) = w (a'.castSucc, s)) (β : B) (i j : Fin n) :
    Commute (weightedHomogeneousComponent w β : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K)) (rE K n m i j) := by
  refine commute_weightedComponent_of_monomial w _ (fun μ => ?_) β
  have h := bm_deriv_monomial_WH (R := K) w 0 (fun v : Fin (n + 1) × Fin m =>
      if v.1 = j.castSucc then (X (i.castSucc, v.2) : MvPolynomial (Fin (n + 1) × Fin m) K) else 0)
    (fun v => by
      split_ifs with hv
      · obtain ⟨a, s⟩ := v
        obtain rfl : a = j.castSucc := hv
        rw [add_zero, hw j i]
        exact isWeightedHomogeneous_X K w _
      · exact isWeightedHomogeneous_zero K w _) μ
  rwa [add_zero, ← rowE_eq_deriv] at h

theorem zcomp_comm_rE (n : ℕ) (β : Fin n → ℤ) (i j : Fin n) : Commute (zcomp K n β) (rE K n n i j) :=
  comp_comm_rE n n (zW n) (fun a a' s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) β i j

theorem lastcomp_comm_rE (n d : ℕ) (i j : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End K (BP K n)) (rE K n n i j) :=
  comp_comm_rE n n (lastW n) (fun a a' s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) d i j

theorem glOperatorFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (i j : Fin n) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rE K n n i j G ∈ bmW K n lam d := by
  rw [bmK_mem_alt] at hG ⊢
  exact ⟨rowE_mem _ _ hG.1, bm_isWH_of_comm (lastW n) d _ (lastcomp_comm_rE n d i j) G hG.2⟩

theorem capelliDeterminantFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (u : ℤ) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rCap K n n u G ∈ bmW K n lam d :=
  capDet_mem _ _ (fun i j _ hx => glOperatorFirstRows_mem_bmW i j hx) u hG

theorem zcomp_comm_rCap (n : ℕ) (β : Fin n → ℤ) (u : ℤ) : Commute (zcomp K n β) (rCap K n n u) :=
  capDet_commute_of _ u _ (zcomp_comm_rE n β)

theorem coeff_rowE_self {r m : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin m) K) (μ : Fin r × Fin m →₀ ℕ) :
    coeff μ (rowE K r m a a f) = (rowDeg μ a : K) * coeff μ f := by
  classical
  rw [rowE_apply, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_X_mul']
  split_ifs with h
  · have h1 : Finsupp.single (a, s) 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [coeff_pderiv, tsub_add_cancel_of_le h1, mul_comm]
    congr 1
    have h2 : 1 ≤ μ (a, s) := Finsupp.single_le_iff.1 h1
    simp [Nat.cast_sub h2]
  · rw [Finsupp.notMem_support_iff.1 h]; simp

theorem rowWeight_iff [CharZero K] {r m : ℕ} (ρ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin m) K) :
    IsWeightedHomogeneous (rowW r m) f ρ ↔ ∀ a, rowE K r m a a f = (ρ a : K) • f := by
  constructor
  · intro h a
    ext μ
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff μ f = 0
    · simp [h0]
    · rw [← bm_weight_rowW, h h0]
  · intro h μ h0
    funext a
    have := congrArg (coeff μ) (h a)
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul] at this
    rw [bm_weight_rowW]
    exact_mod_cast mul_right_cancel₀ h0 this

theorem fockB_eq_zero {σ : Type} (f g : MvPolynomial σ K) (h : ∀ μ, coeff μ f ≠ 0 → coeff μ g = 0) : fockB f g = 0 :=
  Finset.sum_eq_zero fun μ hμ => by rw [h μ (mem_support_iff.1 hμ)]; simp

theorem fockB_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ K) :
    fockB (rename e f) (rename e g) = fockB f g := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    have h1 : ∀ {σ : Type} (g : MvPolynomial σ K), fockB (C a) g = a * constantCoeff g :=
      fun g => @fockL_C_left K _ starRingOfComm _ a g
    rw [rename_C, h1, h1, constantCoeff_rename]
  | add p q hp hq => simp only [← fockBL_apply, map_add, LinearMap.add_apply] at *; rw [hp, hq]
  | mul_X p v hp => rw [mul_comm, map_mul, rename_X, fockB_X_mul, fockB_X_mul, pderiv_rename he, hp]

theorem fockB_incl (n : ℕ) (f g : BP K n) : fockB (incl K n f) (incl K n g) = fockB f g :=
  fockB_rename (Function.injective_id.prodMap (Fin.castSucc_injective n)) f g

end Basic

end GlobalTheory.BrCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExistsStatement
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_of_isCob : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainMemCocyclesStatement
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

open GlobalTheory.AbLaw in

theorem cech_one_cocycle_split : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  intro X U hU K W hW hc f hf
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB X
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU K W hW hc
    (fun a b => (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).symm (f a b)) (by
      intro a b d O ha hb hd
      apply (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).injective
      have h : rs X inf_le_left (f a b) + rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W a ⊓ W b ⊓ W d ≤ W a ⊓ W d) (f a d) := hf a b d
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) h
      simp only [map_add, rs_rs] at h
      rw [map_add, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]
      simpa only [LinearEquiv.apply_symm_apply] using h)
  refine ⟨fun a => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  first | exact @GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | exact GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary | (intros; apply GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOneStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDensity_continuousAt_zero_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧ ∀ τ, (mat x τ).det ≠ 0 := by
  first | exact @GlobalTheory.DensOne.dens_one | exact GlobalTheory.DensOne.dens_one | (intros; apply GlobalTheory.DensOne.dens_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopenCond_injective_geom_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOntoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopenCond_onto_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHomStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  first | exact @GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | exact GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal | (intros; apply GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.CobLead

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
private lemma subst_constantCoeff_zero_and_linear_coeff_eq {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    (w : Fin d ⊕ Fin d → MvPowerSeries τ R) (hw : ∀ s, constantCoeff (w s) = 0)
    (F G : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hFG : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≤ 1 → coeff α F = coeff α G)
    (hG : constantCoeff G = 0) :
    constantCoeff (subst w F) = 0 ∧ constantCoeff (subst w G) = 0 ∧
      ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ (subst w F) = coeff γ (subst w G) := by
  have hlow : ∀ H : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α H = 0) →
      constantCoeff (subst w H) = 0 := by
    intro H hH
    have h := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 1 H hw hw (fun _ _ _ => rfl) hH 0).1
      (by simp)
    rwa [coeff_zero_eq_constantCoeff_apply] at h
  have hG0 : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α G = 0 := by
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hG]
  refine ⟨hlow F (fun α hα => by rw [hFG α hα.le]; exact hG0 α hα), hlow G hG0, ?_⟩
  intro γ hγ
  have hdiff := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 2 (F - G) hw hw (fun _ _ _ => rfl)
    (fun α hα => by rw [map_sub, hFG α (by omega), sub_self]) γ).1 (by omega)
  rw [subst_sub (hasSubst_of_constantCoeff_zero hw), map_sub, sub_eq_zero] at hdiff
  exact hdiff

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.CobLead.cob_eq_additive_lead : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (_root_.GlobalTheory.Katz.addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = coeff γ (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.Katz.addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob2 μ c) = coeff γ (_root_.GlobalTheory.Katz.cob2 (_root_.GlobalTheory.Katz.addLaw R d) c) := by
  intro R _ d μ N hμ
  have hadd0 : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
    intro i
    simp [_root_.GlobalTheory.Katz.addLaw]
  have hμ0 : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hμ i 0 (by simp), coeff_zero_eq_constantCoeff_apply, hadd0]
  have hX : ∀ {ι κ : Type} (e : ι → κ) (s : ι), constantCoeff (X (e s) : MvPowerSeries κ R) = 0 :=
    fun _ _ => by simp
  refine ⟨fun f hf γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun c hc γ hγ => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    rw [map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ μ N f hμ0 hμ0 (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inl) (hX Sum.inl)
        (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inr) (hX Sum.inr)
        (fun _ _ _ => rfl) hf γ).1 hγ]
    simp
  · unfold _root_.GlobalTheory.Katz.cob1
    rw [map_sub, map_sub, map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ (_root_.GlobalTheory.Katz.addLaw R d) N f hμ0 hadd0
        (fun i γ' hγ' => hμ i γ' hγ'.le) hf γ).2 hγ]
  · have hpts : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) →
        (∀ s, constantCoeff (b s) = 0) → ∀ i,
          constantCoeff (_root_.GlobalTheory.Katz.op μ a b i) = 0 ∧
          constantCoeff (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) = 0 ∧
          ∀ γ' : τ →₀ ℕ, γ'.degree = 1 → coeff γ' (_root_.GlobalTheory.Katz.op μ a b i) =
            coeff γ' (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) := by
      intro τ a b ha hb i
      exact subst_constantCoeff_zero_and_linear_coeff_eq (Sum.elim a b) (fun s => by cases s <;> simp [ha, hb])
        (μ i) (_root_.GlobalTheory.Katz.addLaw R d i) (hμ i) (hadd0 i)
    have hs1 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x1]
    have hs2 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x2]
    have hs3 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x3]
    have h12 := hpts _ _ hs1 hs2
    have h23 := hpts _ _ hs2 hs3
    unfold _root_.GlobalTheory.Katz.cob2 _root_.GlobalTheory.Katz.at2
    rw [map_sub, map_add, map_sub, map_sub, map_add, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
          _root_.GlobalTheory.Katz.x3)
        (Sum.elim (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) _root_.GlobalTheory.Katz.x1
          _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3) N c
        (fun s => by rcases s with s | s; exacts [(h12 s).1, hs3 s])
        (fun s => by rcases s with s | s; exacts [(h12 s).2.1, hs3 s])
        (fun s γ' hγ' => by rcases s with s | s; exacts [(h12 s).2.2 γ' hγ', rfl]) hc γ).2 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim _root_.GlobalTheory.Katz.x1
          (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3))
        (Sum.elim _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d)
          _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) N c
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).1])
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).2.1])
        (fun s γ' hγ' => by rcases s with s | s; exacts [rfl, (h23 s).2.2 γ' hγ']) hc γ).2 hγ]

end GlobalTheory.CobLead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEdgesMemOfCoboundaryTwoCoeffsInIdealStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_edges_mem_of_coboundaryTwo_coeffsInIdeal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  first | exact @GlobalTheory.CobEdges.coeff_edges_mem | exact GlobalTheory.CobEdges.coeff_edges_mem | (intros; apply GlobalTheory.CobEdges.coeff_edges_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  first | exact @GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | exact GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | (intros; apply GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero <;> assumption)
end

