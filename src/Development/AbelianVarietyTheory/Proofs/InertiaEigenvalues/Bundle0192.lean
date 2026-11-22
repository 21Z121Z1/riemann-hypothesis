import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIff
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.XiTriv
theorem frobA : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein
theorem limR : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit
theorem growth : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := GlobalTheory.T.tendsto_const_pow_mul_pow_pow_zero'
theorem decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm

theorem convB : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧) (Y : ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ n τ i j, (X : K⟦X⟧) ^ (n + 1) ∣ Y τ i j - Z n τ i j) → ∀ τ i j, Y τ i j ∈ R O K l k := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z Y hB h0 hs hY τ i j
  have h1 : ∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j := fun τ i j => by
    have a1 := hY 0 τ i j
    have a2 := (pow_dvd_pow (X : K⟦X⟧) (by omega : 1 ≤ 2)).trans (hY 1 τ i j)
    rw [pow_one] at a1 a2
    have := dvd_sub a1 a2
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨M, β, hβ, hD⟩ := decay O K l a ι k hk B c Z hB h0 hs h1
  have hr0 : 0 ≤ rad l k := rad_nonneg l k
  have hr1 : rad l k < 1 := rad_lt_one l hk
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  refine limR O K l k (Y τ i j) (fun n => Z n τ i j) (fun n => (hD n τ i j).1) (fun n => hY n τ i j) ?_
  have hg := (growth β (rad l k) l hβ hr0 hr1 hl2).const_mul M
  rw [mul_zero] at hg
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hg
  · have hm := sub_mem (hD (n + 1) τ i j).1 (hD n τ i j).1
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 0)).trans (le_normR hm 0)
  · rw [← mul_assoc]; exact (hD n τ i j).2
end GlobalTheory.BK.XiTriv

noncomputable section

namespace GlobalTheory.BK.XiTriv

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]

theorem frob_map_mul (M N : Matrix ι ι K⟦X⟧) :
    (M * N).map (frob K l) = M.map (frob K l) * N.map (frob K l) :=
  Matrix.map_mul (f := (frob K l).toRingHom)

theorem frob_map_one : (1 : Matrix ι ι K⟦X⟧).map (frob K l) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem dvd_mul_mul_apply {c : K⟦X⟧} (M D N : Matrix ι ι K⟦X⟧) (h : ∀ i j, c ∣ D i j) (i j : ι) :
    c ∣ (M * D * N) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun m _ => (h m k).mul_left _

namespace Seq

variable (P : PhiMod O K l e a ι)

def Ws (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun W τ => (P.mx0 τ).map C * (W (τ - 1)).map (frob K l) * P.mxInv τ)^[n] fun _ => 1

theorem Ws_zero (τ : ZMod a) : Ws P 0 τ = 1 := rfl

theorem Ws_succ (n : ℕ) (τ : ZMod a) : Ws P (n + 1) τ =
    (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * P.mxInv τ := by
  rw [Ws, Function.iterate_succ_apply']
  rfl

theorem Ws_mul (n : ℕ) (τ : ZMod a) : Ws P n τ * P.xiSeq n τ = 1 := by
  induction n generalizing τ with
  | zero => rw [Ws_zero, PhiMod.xiSeq_zero, Matrix.one_mul]
  | succ n ih =>
    have h1 := P.mxInv_mul_mx τ
    have h3 : (P.mx0 τ).map C * ((P.mxInv τ).map constantCoeff).map C = 1 := by
      rw [← Matrix.map_mul, P.matrix_mul_inv_const_eq_one τ, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [PhiMod.xiSeq_succ, Ws_succ]
    calc _ = (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * (P.mxInv τ * P.mx τ) *
          (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
          simp only [Matrix.mul_assoc]
      _ = (P.mx0 τ).map C * ((Ws P n (τ - 1) * P.xiSeq n (τ - 1)).map (frob K l)) *
          ((P.mxInv τ).map constantCoeff).map C := by
          rw [h1, frob_map_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [ih, frob_map_one, Matrix.mul_one, h3]

theorem xiMat_mul_inv (τ : ZMod a) : P.xiMat τ * (P.xiMat τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)

theorem inv_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 2) ∣ ((P.xiMat τ)⁻¹ - Ws P (n + 1) τ) i j := by
  have h : (P.xiMat τ)⁻¹ - Ws P (n + 1) τ =
      Ws P (n + 1) τ * (P.xiSeq (n + 1) τ - P.xiMat τ) * (P.xiMat τ)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Ws_mul, Matrix.one_mul, Matrix.mul_assoc,
      xiMat_mul_inv, Matrix.mul_one]
  rw [h]
  refine dvd_mul_mul_apply _ _ _ (fun i j => ?_) i j
  rw [Matrix.sub_apply, ← neg_sub]
  exact (dvd_neg).2 (P.xiMat_sub_dvd (n + 1) τ i j)

end Seq

variable [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem mulVec_mem {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B)
    {v : ι → K⟦X⟧} (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)

theorem Y_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    (P.mxInv τ * P.xiMat τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  refine convB O K l a ι k hk0 (fun τ => (P.mx (τ - 1)).map (frob K l))
    (fun τ => (P.mxInv τ).map constantCoeff) (fun n τ => P.mxInv τ * P.xiSeq (n + 1) τ)
    (fun τ => P.mxInv τ * P.xiMat τ) (fun τ i j => frobA O K l e k hk _ (P.mx_mem _ i j))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ i j
  · rw [PhiMod.xiSeq_succ, PhiMod.xiSeq_zero, frob_map_one, Matrix.mul_one, ← Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · rw [PhiMod.xiSeq_succ P (n + 1), ← frob_map_mul, ← Matrix.mul_assoc (P.mx (τ - 1)),
      PhiMod.mx_mul_mxInv, Matrix.one_mul, ← Matrix.mul_assoc (P.mxInv τ), ← Matrix.mul_assoc (P.mxInv τ),
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · have h : P.mxInv τ * P.xiMat τ - P.mxInv τ * P.xiSeq (n + 1) τ =
        P.mxInv τ * (P.xiMat τ - P.xiSeq (n + 1) τ) * 1 := by
      rw [Matrix.mul_one, Matrix.mul_sub]
    rw [← Matrix.sub_apply, h]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (P.xiMat_sub_dvd (n + 1) τ i j)) i j

theorem Yi_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    ((P.xiMat τ)⁻¹ * P.mx τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  have key := convB O K l a ι k hk0 (fun τ => ((P.mxInv (τ - 1)).map (frob K l))ᵀ)
    (fun τ => (P.mx0 τ)ᵀ) (fun n τ => (Seq.Ws P (n + 1) τ * P.mx τ)ᵀ)
    (fun τ => ((P.xiMat τ)⁻¹ * P.mx τ)ᵀ) (fun τ i j => frobA O K l e k hk _ (P.mxInv_mem _ j i))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ j i
  · simpa using key
  · show (Seq.Ws P (0 + 1) τ * P.mx τ)ᵀ = ((P.mx0 τ)ᵀ).map C
    rw [Seq.Ws_succ, Seq.Ws_zero, frob_map_one, Matrix.mul_one, Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.mul_one, Matrix.transpose_map]
  · show (Seq.Ws P (n + 2) τ * P.mx τ)ᵀ = ((P.mxInv (τ - 1)).map (frob K l))ᵀ *
        ((Seq.Ws P (n + 1) (τ - 1) * P.mx (τ - 1))ᵀ).map (frob K l) * ((P.mx0 τ)ᵀ).map C
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul,
      ← Matrix.transpose_mul]
    congr 1
    rw [Seq.Ws_succ P (n + 1), Matrix.mul_assoc _ (P.mxInv τ), PhiMod.mxInv_mul_mx, Matrix.mul_one,
      ← frob_map_mul,
      Matrix.mul_assoc (Seq.Ws P (n + 1) (τ - 1)), PhiMod.mx_mul_mxInv, Matrix.mul_one]
  · rw [Matrix.transpose_apply, Matrix.transpose_apply, ← Matrix.sub_apply, ← Matrix.sub_mul,
      ← Matrix.one_mul ((P.xiMat τ)⁻¹ - Seq.Ws P (n + 1) τ)]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (Seq.inv_sub_dvd P n τ i j)) j i

end GlobalTheory.BK.XiTriv

end

open PowerSeries GlobalTheory.BK in
theorem GlobalTheory.BK.xiExt_mem_Lk_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P k hk w
  have hprod (τ : ZMod a) : ((P.xiMat τ)⁻¹ * P.mx τ) * (P.mxInv τ * P.xiMat τ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.mx τ), PhiMod.mx_mul_mxInv, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  constructor
  · intro h
    refine mem_tot.2 fun τ => ?_
    have h1 := P.mem_extc_iff.1 (mem_tot.1 h τ)
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec] at h1
    have h2 := XiTriv.mulVec_mem (XiTriv.Yi_mem P hk τ) h1
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h2
  · intro h
    refine mem_tot.2 fun τ => P.mem_extc_iff.2 ?_
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec]
    exact XiTriv.mulVec_mem (XiTriv.Y_mem P hk τ) (mem_tot.1 h τ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
section
noncomputable section

namespace GlobalTheory.SenLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct PowerSeries

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def serAct (f : F⟦X⟧) (y : ℤ → M) : ℤ → M := fun m => ∑ᶠ j : ℕ, coeff j f • y (m - j)

def serLine (u : ℤ) (d : M) (c : F⟦X⟧) : ℤ → M :=
  fun m => if 0 ≤ m + u then coeff (m + u).toNat c • d else 0

theorem serAct_one (y : ℤ → M) : serAct (1 : F⟦X⟧) y = y := by
  funext m
  rw [serAct, finsum_eq_single _ 0 (fun j hj => by rw [coeff_one, if_neg hj, zero_smul])]
  simp

def SpanIsLines {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (F : Type) [Field F]
    [Module F M] : Prop :=
  ∀ y : ℤ → M, (∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j))) ↔
    ∃ c : Fin r → F⟦X⟧, y = ∑ k, serLine (u k) (d k) (c k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def LinesAt (i : ZMod n) (ζ : LL) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin (Module.finrank LL T.V) → ℤ) (d : Fin (Module.finrank LL T.V) → T.V ⊗[Qp] BdR),
    Finset.univ.val.map u = U ∧ LinearIndependent LL d ∧ SpanIsLines (W.levN T i ζ) u d LL

def QFrame (g : W.Gam) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective J ∧
  (∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  J X = W.π₀₁ + ((PD.p : ℕ) : O⟦X⟧) ∧
  (∀ c, constantCoeff (J c) = 0 → X - ((PD.p : ℕ) : O⟦X⟧) ∣ c) ∧
  (∃ s : (O⟦X⟧)ˣ, W.γ₀ g (J X) = J X * J s ∧ X - ((PD.p : ℕ) : O⟦X⟧) ∣ (s : O⟦X⟧) - 1) ∧
  Associated (J X) W.q₀ ∧
  IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n)))

end Generic

def CompletionLines : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (H : LocHW l P) (F : LocFon l P AI H), LocCmpT l P AI H F →
    ∀ (K LL : FinExt l) (hA : CaseA K LL) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) →
      ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), IsPrimitiveRoot ζ l →
        LinesAt (H.W K 1 LL hA.2.2) T i ζ (U i)

end GlobalTheory.SenLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasisStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  first | exact @GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | exact GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds | (intros; apply GlobalTheory.LocDualTop.dualLat_compact_powSub_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobeniusStatement
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | exact GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | (intros; apply GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmodule
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL.Tconn

theorem N_vpow {K : Type} [NormedField K] (e A' : ℕ) :
    N K (((X : K⟦X⟧) ^ e) ^ A') = ((e * A' : ℕ) : K⟦X⟧) * ((X : K⟦X⟧) ^ e) ^ A' := by
  ext n
  rw [coeff_N, ← pow_mul, ← map_natCast (C (R := K)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem N_lpow {K : Type} [NormedField K] (l b : ℕ) : N K ((l : K⟦X⟧) ^ b) = 0 := by
  rw [← Nat.cast_pow]; exact Derivation.map_natCast _ _

theorem part_top {K O κ : Type} {a : ℕ} [NormedField K] [CommRing O] [Algebra O K]
    (V : Submodule O (Vec K a κ)) : GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ V = V := by
  ext v; simp [GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part]

end GlobalTheory.CokerL.Tconn

theorem GlobalTheory.CokerL.Tsub_conn : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F A' b hred x hx
  have hIS := (hred.2.2 ι κ η H D₁ D₂ F).2.1
  have hMH := (hred.2.1 κ η H D₂).1
  have hvS : ((X : K⟦X⟧) ^ e) ^ A' ∈ S O K e := pow_mem (pow_mem HasU.X_mem e) A'
  have hHigh : ∀ (f : K⟦X⟧), f ∈ S O K e → ∀ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod,
      f • q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod := fun f hf q hq =>
    (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • D₂.MM).smul_mem (⟨f, hf⟩ : S O K e) hq
  have hnat : ∀ (n : ℕ) (q : Vec K a κ) (V : Submodule O (Vec K a κ)), q ∈ V → ((n : K⟦X⟧)) • q ∈ V :=
    fun n q V hq => by
      rw [Nat.cast_smul_eq_nsmul]; exact V.nsmul_mem hq n
  obtain ⟨x12, h12, x3, h3, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨x1, h1, x2, h2, rfl⟩ := Submodule.mem_sup.1 h12
  rw [map_add, map_add]
  refine add_mem (add_mem ?_ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := h1
    change D₂.toPhiMod.conn (((X : K⟦X⟧) ^ e) ^ A' • y) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_vpow, mul_smul]
    refine add_mem ?_ ?_
    · have : ((e * A' : ℕ) : K⟦X⟧) • y ∈ (F.imL.restrictScalars O) := hnat _ _ _ hy
      rw [smul_comm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, this, rfl⟩)
    · have hc := hIS y (by
        rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top]
        exact Submodule.mem_sup_left hy)
      rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
      rw [← hpq, smul_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨p, hp, rfl⟩))
        (Submodule.mem_sup_right (hHigh _ hvS q hq))
  · obtain ⟨z, hz, rfl⟩ := h2
    change D₂.toPhiMod.conn (((l : K⟦X⟧) ^ b) • z) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_lpow, zero_smul, zero_add]
    have hzM : z ∈ D₂.MM := PhiMod.ext_mono _ (A_le_S l e) hz
    have hc : D₂.conn z ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) := by
      rw [GlobalTheory.CokerL.Tconn.part_top]
      exact BKDat.conn_mem_MM D₂ hzM
    rw [hMH.MM_eq, GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
    change (l : K⟦X⟧) ^ b • D₂.toPhiMod.conn z ∈ _
    rw [← hpq, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨p, hp, rfl⟩)) ?_
    refine Submodule.mem_sup_right ?_
    rw [← Nat.cast_pow]
    exact hnat _ _ _ hq
  · have := hMH.conn_high x3 (by rw [GlobalTheory.CokerL.Tconn.part_top]; exact h3)
    rw [GlobalTheory.CokerL.Tconn.part_top] at this
    exact Submodule.mem_sup_right this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGradedStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerE_add_smul_mem_eisenstein_shift_graded : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | exact GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | (intros; apply GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombination
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PSer

theorem emod_toNat_lt (h : ℕ) (hh : 1 ≤ h) (k : ℤ) : (k % (h : ℤ)).toNat < h := by
  have h0 : (0 : ℤ) < h := by exact_mod_cast hh
  have := Int.emod_lt_of_pos k h0
  have := Int.emod_nonneg k h0.ne'
  omega

def reCoef (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) : ℂ_[l] :=
  (l : ℂ_[l]) ^ (-(k / (h : ℤ))) * μ ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩

theorem reCoef_add (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) :
    reCoef l h hh μ k = (l : ℂ_[l]) * reCoef l h hh μ (k + h) := by
  have hl : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have e1 : (k + h) / (h : ℤ) = k / h + 1 := by
    have := Int.add_mul_ediv_right k 1 h0; simpa using this
  have e2 : (k + h) % (h : ℤ) = k % h := by simp
  unfold reCoef
  simp only [e1, e2]
  rw [neg_add, zpow_add₀ hl, zpow_neg_one]
  field_simp

theorem reCoef_at (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (n : ℤ) (i : Fin h) :
    reCoef l h hh μ (n * h + i) = (l : ℂ_[l]) ^ (-n) * μ i := by
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have hih : (i : ℤ) < h := by exact_mod_cast i.isLt
  have e1 : (n * h + i) / (h : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ h0, Int.ediv_eq_zero_of_lt hi0 hih, zero_add]
  have e2 : (n * h + i) % (h : ℤ) = i := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]
  unfold reCoef
  congr 2
  · rw [e1]
  · ext; simp [e2]

theorem emod_at (h : ℕ) (hh : 1 ≤ h) (n : ℤ) (i : Fin h) :
    (n * h + ((i : ℕ) : ℤ)) % (h : ℤ) = ((i : ℕ) : ℤ) := by
  have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
  have hih : ((i : ℕ) : ℤ) < h := by exact_mod_cast i.isLt
  rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]

theorem exists_coef_hasSum_lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 →
    ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧
      ∀ x : Fl l, ‖sh x‖ < 1 →
        HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  intro l _ h μ hh hμ
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  refine ⟨reCoef l h hh μ, reCoef_add l h hh μ, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra H; push_neg at H; exact hμ (funext H)
    refine ⟨((i : ℕ) : ℤ), ?_⟩
    have := reCoef_at l h hh μ 0 i
    simp only [zero_mul, zero_add, neg_zero, zpow_zero, one_mul] at this
    rw [this]; exact hi
  · intro x hx
    let f : ℤ → ℂ_[l] := fun k => reCoef l h hh μ k * sh (pw k x)
    let F : Fin h → ℤ → ℂ_[l] := fun i k => if k % (h : ℤ) = ((i : ℕ) : ℤ) then f k else 0
    have hF : ∀ k, f k = ∑ i, F i k := by
      intro k
      have hn : 0 ≤ k % (h : ℤ) := Int.emod_nonneg k h0
      rw [Finset.sum_eq_single ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩]
      · simp only [F]; rw [if_pos (by simp [Int.toNat_of_nonneg hn])]
      · intro b _ hb
        simp only [F]
        rw [if_neg]
        intro hbk
        apply hb
        ext
        simp only
        omega
      · intro hc; exact absurd (Finset.mem_univ _) hc
    have hFi : ∀ i : Fin h, HasSum (F i) (μ i * lam h i x) := by
      intro i
      have hg : Function.Injective (fun n : ℤ => n * h + ((i : ℕ) : ℤ)) := by
        intro a b e
        have e' : a * (h : ℤ) = b * h := by simpa using e
        exact mul_right_cancel₀ h0 e'
      rw [← hg.hasSum_iff]
      · have := ((GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h i ‖sh x‖ x hh hx le_rfl).1).mul_left (μ i)
        have heq : (F i ∘ fun n : ℤ => n * h + ((i : ℕ) : ℤ)) =
            fun n : ℤ => μ i * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((i : ℕ) : ℤ)) x)) := by
          funext n
          simp only [Function.comp, F, f]
          rw [if_pos (emod_at h hh n i), reCoef_at]
          ring
        rw [heq]; exact this
      · intro k hk
        simp only [F]
        rw [if_neg]
        intro hki
        apply hk
        refine ⟨k / h, ?_⟩
        have := Int.ediv_mul_add_emod k (h : ℤ)
        simp only
        rw [← hki]
        linarith [mul_comm (k / (h : ℤ)) (h : ℤ)]
    have := hasSum_sum (s := Finset.univ) (fun i _ => hFi i)
    have hf : f = fun k => ∑ i, F i k := funext hF
    show HasSum f _
    rw [hf]; exact this

end GlobalTheory.PSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatibleStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  first | exact @GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | exact GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | (intros; apply GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticePairingEqInvUniformizerStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), IsLatticeIn D.T → PerfectRight D.bT → ∀ ϖ : O, Irreducible ϖ → ∀ x : VT ⧸ D.T, x ≠ 0 → ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTripleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e] [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  first | exact @GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | exact GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | (intros; apply GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple <;> assumption)
end

