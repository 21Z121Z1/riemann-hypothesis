import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0013
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0001
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficients
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

private def LowZero {ι K : Type} [Field K] (a : ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m : ι →₀ ℕ, m.degree < a → MvPowerSeries.coeff m f = 0

private theorem lowZero_mul {ι K : Type} [Field K] {a b : ℕ} {f g : MvPowerSeries ι K}
    (hf : LowZero a f) (hg : LowZero b g) : LowZero (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hx', map_add]
  by_cases h : x.1.degree < a
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem lowZero_one {ι K : Type} [Field K] : LowZero 0 (1 : MvPowerSeries ι K) :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

private theorem lowZero_pow {ι K : Type} [Field K] {f : MvPowerSeries ι K}
    (hf : LowZero 1 f) (e : ℕ) : LowZero e (f ^ e) := by
  induction e with
  | zero => simpa using lowZero_one
  | succ e ih => rw [pow_succ]; exact lowZero_mul ih hf

private theorem lowZero_prod {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (ha : ∀ i, LowZero 1 (a i)) (k : ι →₀ ℕ) (s : Finset ι) :
    LowZero (∑ i ∈ s, k i) (∏ i ∈ s, a i ^ k i) := by
  induction s using Finset.induction_on with
  | empty => simpa using lowZero_one
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lowZero_mul (lowZero_pow (ha i) _) ih

private theorem coeff_subst_low {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (hs : MvPowerSeries.HasSubst a) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (W : MvPowerSeries ι K) (d : ℕ) (hW : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0)
    (m : ι →₀ ℕ) (hm : m.degree ≤ d) : MvPowerSeries.coeff m (MvPowerSeries.subst a W) = 0 := by
  have ha1 : ∀ i, LowZero 1 (a i) := by
    intro i n hn
    have hn0 : n = 0 := by
      have : n.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff n).mp this
    rw [hn0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha i]
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  by_cases hk : k.degree ≤ d
  · rw [hW k hk, zero_smul]
  · have h := lowZero_prod a ha1 k k.support m (by
      have : k.degree = ∑ i ∈ k.support, k i := rfl
      omega)
    have e : (k.prod fun s e => a s ^ e) = ∏ i ∈ k.support, a i ^ k i := rfl
    rw [e, h, smul_zero]

theorem low_coeff_of_param (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1]
    [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p))
    (hUn : ∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0))
    (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ))
    (hS : ∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) (m : ι →₀ ℕ) (hm : m.degree ≤ d) :
    MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) *
      algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  have hs := Pf.en_Ec_hs p K1 (ι := ι)
  set c : (ι →₀ ℕ) → K1 := fun n => MvPowerSeries.coeff n (inParamK p K1 U) with hc

  have hmon : ∀ n, MvPowerSeries.subst (Pf.en_Ec p K1) (MvPowerSeries.monomial n (1 : K1)) =
      MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    intro n
    have h1 : inParamK p K1 (MvPowerSeries.map (algebraMap (K0 p) K1) (Un n)) =
        MvPowerSeries.monomial n (1 : K1) := by
      have h2 := Pf.th_inParamK_map p (K0 p) K1 (Un n)
      rw [h2, ← Pf.th_inParam_eq, (hUn n).1]
      ext k
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
      split_ifs <;> simp
    rw [← h1, Pf.en_Ec_inParamK]
  set W : MvPowerSeries ι K1 := inParamK p K1 U - ∑ n ∈ S, c n • MvPowerSeries.monomial n (1 : K1) with hWdef
  have hWlow : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0 := by
    intro k hk
    have hkS := hS k hk
    rw [hWdef, map_sub, map_sum]
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq S k]
    simp [hkS, hc]
  have hV : MvPowerSeries.subst (Pf.en_Ec p K1) W =
      U - ∑ n ∈ S, c n • MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    rw [← MvPowerSeries.coe_substAlgHom hs, hWdef, map_sub, map_sum, MvPowerSeries.coe_substAlgHom hs,
      Pf.en_Ec_inParamK]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← MvPowerSeries.coe_substAlgHom hs, map_smul, MvPowerSeries.coe_substAlgHom hs, hmon n]
  have h0 := coeff_subst_low (Pf.en_Ec p K1) hs (Pf.en_Ec_zero p K1) W d hWlow m hm
  rw [hV, map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hc, smul_eq_mul]

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulVecMemColSpan
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct Matrix

namespace GlobalTheory.TwV.LbB

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

def FrAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F

def IntB (A : LocAt F E n G) (v : Fin G.P.nV) (t : Fin n → G.P.Qq v) : Prop :=
  ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
    Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ (fun k => A.eQ v (t k))) a ∈ (A.pl v).1.adicCompletionIntegers F

theorem intB_zero (A : LocAt F E n G) (v : Fin G.P.nV) : IntB A v 0 := by
  intro a
  have : (fun k => A.eQ v ((0 : Fin n → G.P.Qq v) k)) = 0 := by funext k; simp
  rw [this, Matrix.mulVec_zero]
  exact zero_mem _

theorem intB_add (A : LocAt F E n G) (v : Fin G.P.nV) (t t' : Fin n → G.P.Qq v) (h : IntB A v t) (h' : IntB A v t') :
    IntB A v (t + t') := by
  intro a
  have : (fun k => A.eQ v ((t + t') k)) = (fun k => A.eQ v (t k)) + (fun k => A.eQ v (t' k)) := by funext k; simp
  rw [this, Matrix.mulVec_add]
  exact add_mem (h a) (h' a)

theorem intB_smul (A : LocAt F E n G) (hW : LocInt A) (v : Fin G.P.nV) (c : G.P.W v) (t : Fin n → G.P.Qq v) (h : IntB A v t) :
    IntB A v (c • t) := by
  intro a
  have : (fun k => A.eQ v ((c • t) k)) = A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) c) • (fun k => A.eQ v (t k)) := by
    funext k
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl
  rw [this, Matrix.mulVec_smul]
  exact mul_mem ((hW v _).1 ⟨c, rfl⟩) (h a)

theorem mulVec_inv_mulVec {R : Type} [CommRing R] (y : GL (Fin n) R) (u : Fin n → R) :
    (y : Matrix (Fin n) (Fin n) R) *ᵥ (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mem_colSpan {Qq W : Type} [CommRing W] [Field Qq] [Algebra W Qq] (M : Matrix (Fin n) (Fin n) Qq) (r : Fin n → W) :
    M *ᵥ (fun c => algebraMap W Qq (r c)) ∈ colSpan W M := by
  have : M *ᵥ (fun c => algebraMap W Qq (r c)) = ∑ c, r c • (fun i => M i c) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem fst_mem_span (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (v : Fin G.P.nV)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F)
    (hx : x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb) :
    (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) ∈
      Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
  unfold Formalism.L2.Herm.locL latS at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((0 : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F) a)).1)) = 0 := by
      funext a; simp
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((x + y) a)).1)) =
        (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) + (fun a => (A.eQ v).symm ((A.spl v (y a)).1)) := by
      funext a; simp
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    have hs := (split_integral_completion F E (A.pl v).1 (A.spl v) (hAlg v) s).1 s.2
    obtain ⟨c, hc⟩ := (hW v ((A.eQ v).symm ((A.spl v s).1))).2 (by rw [RingEquiv.apply_symm_apply]; exact hs.1)
    have : (fun a => (A.eQ v).symm ((A.spl v ((s • x) a)).1)) = c • (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) := by
      funext a
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, map_mul, Pi.smul_apply, Algebra.smul_def, hc]
    rw [this]
    exact Submodule.smul_mem _ c hx

set_option maxHeartbeats 400000 in

theorem lbAt_gen (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) (v : Fin G.P.nV) :
    Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) =
      colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) := by
  set fr : GL (Fin n) ((A.pl v).1.adicCompletion F) := bc (A.phE v) A.B with hfrdef
  have hM : ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) =
      (fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) := by
    ext a b; rfl

  have h1 : ∀ t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))), IntB A v t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have hloc : (fun k => inclE (F := F) ((A.pl v).1.adicCompletion F) (y k)) ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have := (hfr v (fun k => A.eQ v (A.iw v (y k)))).1 ⟨_, hloc, fun a => by
        show (A.ph v) (inclE (F := F) ((A.pl v).1.adicCompletion F) (y a)) = A.eQ v ((A.eQ v).symm (A.phE v (y a)))
        rw [RingEquiv.apply_symm_apply]
        rfl⟩
      exact this
    | zero => exact intB_zero A v
    | add x y _ _ hx hy => exact intB_add A v x y hx hy
    | smul c x _ hx => exact intB_smul A hW v c x hx

  have h2 : ∀ t, IntB A v t → ∃ r : Fin n → G.P.W v,
      t = ((fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)) *ᵥ
        (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) := by
    intro t ht
    choose r hr using fun c => (hW v ((A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => A.eQ v (t k))) c))).2 (by rw [RingEquiv.apply_symm_apply]; exact ht c)
    refine ⟨r, ?_⟩
    have e1 : (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) =
        fun c => (A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) c) := by
      funext c; exact hr c
    rw [e1]
    funext i
    have e2 := RingHom.map_mulVec ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (fr : Matrix (Fin n) (Fin n) _)
      (((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) i
    rw [mulVec_inv_mulVec] at e2
    exact (RingEquiv.symm_apply_apply (A.eQ v) (t i)).symm.trans e2

  have h3 : ∀ t, IntB A v t →
      t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
    intro t ht
    obtain ⟨x, hx, hxa⟩ := (hfr v (fun k => A.eQ v (t k))).2 ht
    have h4 := fst_mem_span A hW hAlg v Lb x hx
    have e3 : (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) = t := by
      funext a; rw [hxa a]; exact RingEquiv.symm_apply_apply _ _
    rw [e3] at h4
    exact h4
  apply le_antisymm
  · intro t ht
    obtain ⟨r, rfl⟩ := h2 t (h1 t ht)
    rw [hM]
    exact mulVec_mem_colSpan _ r
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    apply h3
    intro a
    have hcol : (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c)) =
        fun k => (fr : Matrix (Fin n) (Fin n) _) k c := by
      funext k; rw [hM, Matrix.map_apply]; exact RingEquiv.apply_symm_apply _ _
    show ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
      (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c))) a ∈ _
    rw [hcol]
    have e4 : (((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ
        fun k => (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) k c) a =
        ((((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *
          (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) a c) := by
      simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [e4, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem frAtB_re [StarRing E] {r N : ℕ} (h : r = N) (A : LocAt F E N G) (Lb : Submodule (𝓞 E) (Fin r → E)) (B0 : GL (Fin r) E)
    (hB : A.B = Formalism.L2.Forms.reGL h E B0) (fr : ∀ v, GL (Fin r) ((A.pl v).1.adicCompletion F))
    (hfr0 : ∀ v (t : Fin r → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
        ∀ a, ((((fr v)⁻¹ : GL (Fin r) ((A.pl v).1.adicCompletion F)) :
          Matrix (Fin r) (Fin r) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hrat : ∀ v, fr v = bc (A.phE v) B0) :
    FrAtB A (Lb.map (((reE (E := E) h : (Fin r → E) ≃ₗ[E] (Fin N → E)) : (Fin r → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))) := by
  subst h
  rw [Formalism.MainNotions.G.KAat.map_reE_rfl]
  have hre : Formalism.L2.Forms.reGL (rfl : r = r) E B0 = B0 := by apply Units.ext; ext a b; rfl
  rw [hre] at hB
  intro v t
  rw [hB, ← hrat v]
  exact hfr0 v t

end Gen

section Of

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

theorem lbAtB_of (A : LocAt F E n G) (hW : LocInt A) (hAlg : SplAlg A)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) : GlobalTheory.TwV.LbAtB A Lb := by
  intro v
  unfold GlobalTheory.TwV.locSp
  exact lbAt_gen A hW hAlg Lb hfr v

end Of

end GlobalTheory.TwV.LbB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeConditionsSelectedSet
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.prime_conditions_selected_set : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → (∀ P : rowSG Pr sel mu, (qOf P.1).Prime ∧ ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) ∧ Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) ∧ ∀ u : Pr.Word, Disjoint (Pr.vT u) (rowSG Pr sel mu) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr R Ch sel S mu cst hX hPr hsel hg hT
  have nat : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ), (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := fun P n => by
    rw [mem_conjP, map_natCast]
  have hTm : ∀ u, ∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal := fun u P hP =>
    hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ ((GlobalTheory.MuOffMove.mem_vT hPr u P).1 hP)
  have hGm : ∀ P ∈ Pr.vGs, ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := fun P hP => by
    obtain ⟨i, hi⟩ := GlobalTheory.NormOneUnit.mem_vGs hP
    exact ⟨i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ hi⟩
  refine ⟨fun P => (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1,
    GlobalTheory.NormOneUnit.disjoint_vGs_QE mu hPr hsel hg, fun u => ⟨?_, fun P hP hP' => ?_⟩⟩
  · exact Finset.disjoint_left.2 fun P h h' => GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h' (hTm u P h)
  · rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
    · exact GlobalTheory.MuOffMove.conjP_notMem_vT hPr h h'
    · exact GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h' ((nat P _).2 (hTm u P h))
    · exact GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h ((nat P _).1 (hTm u _ h'))
    · rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
      · exact GlobalTheory.NormOneUnit.conjP_notMem_vGs hPr h h'
      · obtain ⟨i, hi⟩ := hGm P h
        exact GlobalTheory.MuOffMove.notMem_of_mem_QE hsel h' (hPr.g_prime i) (hg i) ((nat P _).2 hi)
      · obtain ⟨i, hi⟩ := hGm _ h'
        exact GlobalTheory.MuOffMove.notMem_of_mem_QE hsel h (hPr.g_prime i) (hg i) ((nat P _).1 hi)
      · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.FibPow

theorem smoothOfRelativeDimension_pow {X : Scheme.{0}} (A : Over X) (g : ℕ)
    (hA : SmoothOfRelativeDimension g A.hom) (k : ℕ) : SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  let e : GlobalTheory.KS.pow A k ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A k :=
    (limit.isLimit (Discrete.functor fun _ : Fin k => A)).conePointUniqueUpToIso
      (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A k)
  have hw : (GlobalTheory.KS.pow A k).hom = e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom := (Over.w e.hom).symm
  have h1 := GlobalTheory.smoothOfRelativeDimension_powObj A g hA k
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + k * g) (e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom) :=
    inferInstance
  rw [hw]; simpa using h2

theorem smoothOfRelativeDimension_fibrePower : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d g : ℕ),
    SmoothOfRelativeDimension d s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ k : ℕ, SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ X s d g hs A _ _ _ hA k
  have h := smoothOfRelativeDimension_pow A g hA k
  have h2 : SmoothOfRelativeDimension (k * g + d) ((GlobalTheory.KS.pow A k).hom ≫ s) := inferInstance
  rw [Nat.add_comm]; exact h2

end GlobalTheory.FibPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def TranslateInt {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (π : X.E) (κ : ℂ) (e : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ (s : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * π) • s ∈ per A N N' →
    GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (κ * jetC A.cD (Wx A s (A.e a b N N')) e)

def HalfInclusions : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p cA c : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    SplitSet A a b S ϖ p → (∀ P ∈ SG, P ∈ S ∧ ϖ ∉ P.asIdeal) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → p ∣ c →
    ∃ (n₀ k : ℕ) (r : 𝓞 X.E), Nat.Coprime n₀ p ∧ r ≠ 0 ∧
      (∀ y ∈ per A N N', ((n₀ : X.E) * (ϖ : X.E) ^ (k + 1)) • y ∈ halfBO S (per A N N') c) ∧
      (∀ y ∈ halfBO S (per A N N') c, (c : X.E) • y ∈ per A N N' ∧
        (star (r : X.E) • y ∈ per A N N' → ((n₀ : X.E) * star (ϖ : X.E)) • y ∈ per A N N')) ∧
      (∀ x ∈ homAt (divs ϖ) N N', ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') →
        (n₀ : X.E) • t ∈ per A N N') ∧
      (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (r : X.E) • y ∈ halfAO S (per A N N') (cA * c) ∧
        (r : X.E) • y ∈ mulLat p (homAt (divs ϖ) N N') ∧ (r : X.E) • y ∈ mulLat c (homAt SG N N') ∧
        ((r : X.E) • y ∈ mulLat c (homAt S N N') ↔ y ∈ smulLat ((ϖ : X.E) ^ k) (per A N N')) ∧
        (y ∈ mulLat c (homAt S N N') → y ∈ halfBO S (per A N N') c)) ∧
      (∀ y ∈ mulLat c (homAt S N N'), y ∈ mulLat p (homAt (divs ϖ) N N') ∧ y ∈ mulLat c (homAt SG N N') ∧
        y ∈ divLat cA (homAt S N N'))

def MultipleIndex : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → p ≠ 0 →
    ϖ * X.conjO ϖ = (p : 𝓞 X.E) →
    (smulLat (ϖ : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup = p ^ (X.f * a * b)

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TranslatesAt {X : Fields} (Pr : Primes X) (A : Amb X) : Prop :=
  ∀ (i : Fin 2) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p = Pr.g i →
    ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b →
      IsSdLat N → IsSdLat N' → StdOver p N → StdOver p N' →
      ∀ e : DVar X.Tau a b →₀ ℕ, e.degree + 1 < p →
        TranslateInt A N N' lam ((Pr.piG i : 𝓞 X.E) : X.E)
          (A.σ₀ (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n)) e

def RecordTranslates : Prop :=
  ∀ (D : D7) (EX : ErrX D) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    HostTie EX → AnTie D δ χ cD → B.VecP χ → B.IntP χ → GlobalTheory.ColPeriod.LatticeFactsAt (ambOf (recSeam D) B χ cD) →
    TranslatesAt (recPrimes EX) (ambOf (recSeam D) B χ cD)

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbitStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  first | exact @GlobalTheory.HTW.Rec.reads_orbit_invFrob | exact GlobalTheory.HTW.Rec.reads_orbit_invFrob | (intros; apply GlobalTheory.HTW.Rec.reads_orbit_invFrob <;> assumption)
end

