import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.LocalToGlobal.LocalInduction.BridgeInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixRe
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.StableSubMat

theorem exists_restrict {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (V : Submodule L (Fin a → L)) (hV : IsInv τ V) :
    ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L),
      D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧
      ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) =
          D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧
        ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
          E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  classical
  set b := Module.finrank L V
  let f : (Fin b → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective
  have hfr : LinearMap.range f = V := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE
  set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD
  have hEf : E.mulVecLin = f := by rw [hE]; exact Matrix.toLin'_toMatrix' f
  have hDf : D.mulVecLin = g₀ := by rw [hD]; exact Matrix.toLin'_toMatrix' g₀
  have hDE : D * E = 1 := by
    rw [hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]
  have hrange : LinearMap.range E.mulVecLin = V := by rw [hEf, hfr]

  have hED : ∀ v ∈ V, (E * D).mulVec v = v := by
    intro v hv
    rw [← hfr] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [← Matrix.mulVec_mulVec]
    have h1 : D.mulVec (f w) = g₀ (f w) := by rw [← hDf]; rfl
    have h2 : ∀ u, E.mulVec u = f u := fun u => by rw [← hEf]; rfl
    rw [h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]
  have key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
      ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E := by
    intro g
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]
    apply hED
    rw [← Matrix.mulVec_mulVec]
    apply hV
    rw [← hrange]
    exact ⟨x, rfl⟩
  let σm : Γ →* Matrix (Fin b) (Fin b) L :=
    { toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E
      map_one' := by simp [hDE]
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul]
        have k := key h
        simp only [Matrix.mul_assoc] at k ⊢
        rw [k] }
  refine ⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.coe_toHomUnits]; rfl
  · rw [MonoidHom.coe_toHomUnits]
    change _ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)
    have k := key g
    simp only [Matrix.mul_assoc] at k ⊢
    exact k.symm

end GlobalTheory.StableSubMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubring
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem image_finite_mem_subring (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  refine ⟨s.image (fun x => iq (algebraMap O (FractionRing O) x)), ?_⟩
  intro R hR hT x
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact hT (by simpa using Finset.mem_image_of_mem (fun x => iq (algebraMap O (FractionRing O) x)) hy)
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, map_mul, map_mul, hiq]
    exact R.mul_mem (hR c) ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImage
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescends
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
      using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  first | exact @GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | exact GlobalTheory.MemLoc.mem_FilD_iff_xi_pow | (intros; apply GlobalTheory.MemLoc.mem_FilD_iff_xi_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEqOneOfVEqZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocArith

variable {l : ℕ} [Fact l.Prime]

theorem v_nonneg_iff (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) :
    0 ≤ P.v LL y ↔ ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := by
  rw [P.v_O]
  exact GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y

theorem norm_natCast_prime : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_eq_one_of_v_eq_zero (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) (hy : P.v LL y = 0) :
    ‖((y : ↥LL.1) : Om l)‖ = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hy
    exact WithTop.top_ne_zero hy
  have h1 : ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL y).1 (hy ▸ le_rfl)
  have hinv : P.v LL y⁻¹ = 0 := by
    have h := (P.v LL).map_mul y y⁻¹
    rw [mul_inv_cancel₀ hy0, AddValuation.map_one, hy, zero_add] at h
    exact h.symm
  have h2 : ‖((y⁻¹ : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL _).1 (hinv ▸ le_rfl)
  have hc : ((y : ↥LL.1) : Om l) ≠ 0 := by simpa using hy0
  have hpos : 0 < ‖((y : ↥LL.1) : Om l)‖ := norm_pos_iff.2 hc
  rw [IntermediateField.coe_inv, norm_inv, inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h2

theorem norm_of_v_eq (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (r : ℚ)
    (hx : P.v LL x = ((r : ℚ) : WithTop ℚ)) :
    ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(r : ℝ)) := by
  set n := r.den with hn
  set a := r.num.toNat with ha
  set b := (-r.num).toNat with hb
  have hkab : (r.num : ℚ) = (a : ℚ) - (b : ℚ) := by
    have : r.num = (a : ℤ) - (b : ℤ) := by simp [ha, hb]
    exact_mod_cast this
  have hnr : (n : ℚ) * r = (a : ℚ) - b := by rw [mul_comm, hn, Rat.mul_den_eq_num, hkab]
  have hL0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := x ^ n * (l : ↥LL.1) ^ b / (l : ↥LL.1) ^ a with hy
  have hya : y * (l : ↥LL.1) ^ a = x ^ n * (l : ↥LL.1) ^ b := div_mul_cancel₀ _ (pow_ne_zero _ hL0)
  have hvy : P.v LL y = 0 := by
    have h := congrArg (P.v LL) hya
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
      AddValuation.map_pow, P.v_l, hx] at h
    have e1 : (n • ((r : ℚ) : WithTop ℚ)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
    have e2 : ∀ m : ℕ, m • (1 : WithTop ℚ) = (((m : ℚ) : ℚ) : WithTop ℚ) := fun m => by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
    rw [e1, e2, e2, hnr] at h
    by_cases ht : P.v LL y = ⊤
    · rw [ht, WithTop.top_add] at h
      exact absurd h.symm (WithTop.coe_ne_top)
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
      rw [← hs] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h
      have : s = 0 := by linarith
      rw [this, WithTop.coe_zero]
  have hN := congrArg (fun z : ↥LL.1 => ‖((z : ↥LL.1) : Om l)‖) hya
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow,
    norm_mul, norm_pow] at hN
  have hc : (((l : ℕ) : ↥LL.1) : Om l) = ((l : ℕ) : Om l) := map_natCast (IntermediateField.val LL.1) l
  rw [norm_eq_one_of_v_eq_zero P LL y hvy, hc, norm_natCast_prime] at hN
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn0 : n ≠ 0 := r.den_nz
  have hxn : ‖((x : ↥LL.1) : Om l)‖ ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [inv_pow, inv_pow, one_mul] at hN
    have hb0 : (0 : ℝ) < (l : ℝ) ^ b := pow_pos hpos b
    have ha0 : (0 : ℝ) < (l : ℝ) ^ a := pow_pos hpos a
    field_simp at hN ⊢
    linarith
  have hrn : ((l : ℝ) ^ (-(r : ℝ))) ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    have : -(r : ℝ) * (n : ℝ) = (b : ℝ) - (a : ℝ) := by
      have h2 : ((n : ℚ) * r : ℚ) = (a : ℚ) - b := hnr
      have h3 : ((n : ℝ) * (r : ℝ)) = (a : ℝ) - b := by exact_mod_cast h2
      linarith
    rw [this, Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]
  rw [← hrn] at hxn
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) hn0).1 hxn

theorem v_eq_iff (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (q : ℚ) :
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  refine ⟨norm_of_v_eq P LL x q, fun h => ?_⟩
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (l : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos hpos _
    simp at h
    linarith
  have ht : P.v LL x ≠ ⊤ := fun ht => hx0 ((P.v LL).top_iff.1 ht)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
  have h2 := norm_of_v_eq P LL x s hs.symm
  rw [h2] at h
  have hqs : (q : ℝ) = (s : ℝ) := by
    have := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 h.le) ((Real.rpow_le_rpow_left_iff hl1).1 h.ge)
    linarith
  rw [← hs, show q = s by exact_mod_cast hqs]

theorem norm_chiQ_le_one (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (one_pow _)
  rw [Nat.cast_zero, neg_zero, zpow_zero] at ha
  have hA : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1 := by
    have := IsUltrametricDist.norm_intCast_le_one ℚ_[l] (a : ℤ)
    simpa using this
  calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
      = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖((a : ℕ) : ℚ_[l])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ha hA

def chiInt (P : LocPrime l) (g : GQ l) : ℤ_[l] := ⟨(P.χQ g : ℚ_[l]), norm_chiQ_le_one P g⟩

theorem arithTied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), Formalism.L2.ArithTied P := fun l _ P =>
  ⟨fun LL x q => v_eq_iff P LL x q⟩

end GlobalTheory.LocArith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
section
noncomputable section

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}

theorem stepLevel_uloc_le_of_agree {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F)))
    (hQ : ∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → x ∈ S.U → x ∈ S'.U)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Q) : S.Uloc v ≤ S'.Uloc v := by
  intro h hh
  have hx1 : bc (prV (E := E) v) (Formalism.UG.P.afsplitU v h 1) = h := Formalism.UG.P.afsplit_right1 v h 1
  have hxw : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
    intro w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
      Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxU : Formalism.UG.P.afsplitU v h 1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v σ J h 1 (S.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, hx1]; exact hh
    · rw [hxw w hw]; exact one_mem _
  have hxQ : ∀ w ∈ Q, bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 :=
    fun w hw => hxw w (fun he => hv (he ▸ hw))
  have h2 := ((S'.U_eq _).mp (hQ _ hxQ hxU)).2 v
  rwa [hx1] at h2

end

theorem stepLevel_uloc_eq_of_agree : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))),
    (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad bad' S S' Q hQ v hv
  exact le_antisymm (stepLevel_uloc_le_of_agree S S' Q (fun x hx => (hQ x hx).mp) v hv)
    (stepLevel_uloc_le_of_agree S' S Q (fun x hx => (hQ x hx).mpr) v hv)

end GlobalTheory
end
end

