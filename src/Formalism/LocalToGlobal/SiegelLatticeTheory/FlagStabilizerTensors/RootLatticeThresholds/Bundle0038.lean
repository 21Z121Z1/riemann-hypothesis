import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0008
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsConv
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsConv

open Formalism.MainNotions.S Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.unitaryCongruence

variable (I : AutInst)

def coset (m : ℕ) (q : KSub I ⧸ KgN I m) : Set I.Gf := {y | ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m}

theorem coset_sub (m : ℕ) (q : KSub I ⧸ KgN I m) : coset I m q ⊆ I.Kset := by
  intro y hy
  have h1 : ((q.out : KSub I) : I.Gf) * (((q.out : KSub I) : I.Gf)⁻¹ * y) ∈ I.Kset :=
    K_mul I (q.out : KSub I).2 hy.1
  simpa using h1

theorem mem_coset_iff (m : ℕ) {y : I.Gf} (hy : y ∈ I.Kset) (q : KSub I ⧸ KgN I m) :
    y ∈ coset I m q ↔ q = (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m) := by
  constructor
  · intro h
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 h
  · intro h
    subst h
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m))
    exact this

theorem isOpen_coset (m : ℕ) (hm : 1 ≤ m) (q : KSub I ⧸ KgN I m) : IsOpen (coset I m q) :=
  (I.topf_open m hm).preimage (continuous_const.mul continuous_id)

theorem measure_coset (μf : Measure I.Gf) [μf.IsMulLeftInvariant] (m : ℕ) (q : KSub I ⧸ KgN I m) :
    μf (coset I m q) = μf (I.Kg m) :=
  measure_preimage_mul μf _ (I.Kg m)

theorem term_eq {m : ℕ} {f₁ f₂ : I.Gf → ℂ} (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y)
    (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) (q : KSub I ⧸ KgN I m) {y : I.Gf}
    (hyq : y ∈ coset I m q) :
    f₁ y * f₂ (y⁻¹ * x) = f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  have hn : ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m := hyq
  generalize ((q.out : KSub I) : I.Gf) = c at hn ⊢
  have e1 : f₁ y = f₁ c := by
    have := h1N c (c⁻¹ * y) hn
    rwa [mul_inv_cancel_left] at this
  have e2 : f₂ (y⁻¹ * x) = f₂ (c⁻¹ * x) := by
    have := h2N (y⁻¹ * x) (c⁻¹ * y) hn
    rw [← this]
    congr 1
    group
  rw [e1, e2]

theorem convF_fin (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {m : ℕ} (hm : 1 ≤ m) (hfin : μf (I.Kg m) < ⊤)
    [Fintype (KSub I ⧸ KgN I m)] {f₁ f₂ : I.Gf → ℂ} (h1K : ∀ y, f₁ y ≠ 0 → y ∈ I.Kset)
    (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y) (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) :
    I.convF μf f₁ f₂ x = (μf (I.Kg m)).toReal *
      ∑ q : KSub I ⧸ KgN I m, f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  classical
  have key : (fun y => f₁ y * f₂ (y⁻¹ * x)) = fun y => ∑ q : KSub I ⧸ KgN I m,
      Set.indicator (coset I m q)
        (fun _ => f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x)) y := by
    funext y
    by_cases hy : y ∈ I.Kset
    · rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)]
      · have hmem := (mem_coset_iff I m hy (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)).2 rfl
        rw [Set.indicator_of_mem hmem]
        exact term_eq I h1N h2N x _ hmem
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hq ((mem_coset_iff I m hy q).1 hmem)
      · intro h; exact absurd (Finset.mem_univ _) h
    · have h0 : f₁ y = 0 := by by_contra h; exact hy (h1K y h)
      rw [h0, zero_mul]
      symm
      refine Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hy (coset_sub I m q hmem)) _
  unfold AutInst.convF
  rw [key, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (isOpen_coset I m hm q).measurableSet, measureReal_def, measure_coset,
      Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (isOpen_coset I m hm q).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_coset]
    exact hfin.ne

end Formalism.L2.SG.Pf.AllRowsConv
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKCRT
section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsKCRT

open NumberField Matrix IsDedekindDomain Formalism.MainNotions.S Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def pm (u : R) (X : Matrix n n R) : Matrix n n R := 1 + u • (X - 1)

theorem pm_one (u : R) : pm u (1 : Matrix n n R) = 1 := by simp [pm]

theorem pm_sub_one (u : R) (X : Matrix n n R) : pm u X - 1 = u • (X - 1) := by simp [pm]

theorem one_add_mul_one_add (a b : Matrix n n R) : (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring

theorem pm_mul {u : R} (hu : u * u = u) (X Y : Matrix n n R) : pm u X * pm u Y = pm u (X * Y) := by
  have e : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold pm
  rw [one_add_mul_one_add, smul_mul_smul_comm, hu, e, smul_add, smul_add]
  abel

theorem pm_mul_compl {u v : R} (h0 : u * v = 0) (h1 : u + v = 1) (X : Matrix n n R) : pm u X * pm v X = X := by
  unfold pm
  rw [one_add_mul_one_add, smul_mul_smul_comm, h0, zero_smul, add_zero, add_assoc, ← add_smul, h1, one_smul]
  abel

theorem cT_pm (σ : R →+* R) {u : R} (hu : σ u = u) (X : Matrix n n R) :
    Formalism.UG.cT σ (pm u X) = pm u (Formalism.UG.cT σ X) := by
  ext a b
  simp only [Formalism.UG.cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hu, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

theorem pm_form {u : R} (hu : u * u = u) (A J X : Matrix n n R) (h : A * J * X = J) :
    pm u A * J * pm u X = J := by
  have e : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = A * J * X - J := by noncomm_ring
  have e0 : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = 0 := by rw [e, h, sub_self]
  have key : (A - 1) * J * (X - 1) = -((A - 1) * J + J * (X - 1)) := eq_neg_of_add_eq_zero_right e0
  have e3 : ∀ a b : Matrix n n R, (1 + a) * J * (1 + b) = J + a * J + J * b + a * J * b := by
    intro a b; noncomm_ring
  unfold pm
  rw [e3, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, hu, key, smul_neg, smul_add]
  abel

end Alg

section Ad

variable {F : Type} [Field F] [NumberField F]

open LatDictZ.Z5

def Tm (m : ℕ) : Set (HeightOneSpectrum (𝓞 F)) := {v | ((m : ℕ) : 𝓞 F) ∈ v.asIdeal}

theorem natc (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (m : Af F) v = algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F) := by
  rw [map_natCast]
  exact map_natCast (ev v) m

theorem comp_sub (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a - b) v = a v - b v := map_sub (ev v) a b

theorem eT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : eT T * eT T = eT T := by
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul]
  by_cases hv : v ∈ T
  · rw [eT_of_mem hv, one_mul]
  · rw [eT_of_not hv, zero_mul]

theorem not_mem_of_coprime {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) {v : HeightOneSpectrum (𝓞 F)}
    (h1 : v ∈ Tm (F := F) m₁) : ((m₂ : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h2
  have hz := Nat.gcd_eq_gcd_ab m₁ m₂
  rw [h, Nat.cast_one] at hz
  have hO := congrArg (Int.cast : ℤ → 𝓞 F) hz
  push_cast at hO
  have h1' : ((m₁ : ℕ) : 𝓞 F) ∈ v.asIdeal := h1
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [hO]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1') (Ideal.mul_mem_right _ _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

open Classical in
theorem compl_eq (m : ℕ) : ∃ c ∈ Formalism.UG.intAd F, 1 - eT (Tm (F := F) m) = (m : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F))⁻¹)
    (fun v => by split_ifs with h; exacts [zero_mem _, inv_mem' h]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_sub, LatDictZ.Z5.comp_one, comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m
  · rw [eT_of_mem hv, if_pos hv, sub_self, mul_zero]
  · rw [eT_of_not hv, if_neg hv, sub_zero, mul_inv_cancel₀ (ne0 hv)]

open Classical in
theorem idem_eq {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) :
    ∃ c ∈ Formalism.UG.intAd F, eT (Tm (F := F) m₁) = (m₂ : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m₁ then (algebraMap (𝓞 F) (v.adicCompletion F) (m₂ : 𝓞 F))⁻¹ else 0)
    (fun v => by split_ifs with hv; exacts [inv_mem' (not_mem_of_coprime h hv), zero_mem _]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m₁
  · rw [eT_of_mem hv, if_pos hv, mul_inv_cancel₀ (ne0 (not_mem_of_coprime h hv))]
  · rw [eT_of_not hv, if_neg hv, mul_zero]

end Ad

section Inst

variable (I : AutInst)

open LatDictZ.Z5

theorem sig_iA (a : Af I.F) : Formalism.UG.sigR I.cm.sig (Af I.F) (iA I a) = iA I a := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem fmat_mul_inv' (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  rw [← fmat_mul, mul_inv_cancel, fmat_one]

def mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) : I.Gf :=
  ⟨⟨pm u (I.fmat x), pm u (I.fmat x⁻¹),
    by rw [pm_mul hu, fmat_mul_inv', pm_one], by rw [pm_mul hu, fmat_inv_mul, pm_one]⟩, by
    have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (pm u (I.fmat x)) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        pm u (I.fmat x) = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_pm _ hσ]
    exact pm_form hu _ _ _ hx⟩

theorem fmat_mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) :
    I.fmat (mkG I u hu hσ x) = pm u (I.fmat x) := rfl

theorem smul_Lf {u : I.E ⊗[I.F] Af I.F} (hI : u ∈ IntAf I.F I.E) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : u • y ∈ I.Lf :=
  I.Lf.smul_mem ⟨u, hI⟩ hy

theorem pm_mv_mem {u : I.E ⊗[I.F] Af I.F} (hI : u ∈ IntAf I.F I.E) {x : I.Gf} (hx : x ∈ I.Kset)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) : pm u (I.fmat x) *ᵥ y ∈ I.Lf := by
  have e : pm u (I.fmat x) *ᵥ y = y + u • ((I.fmat x - 1) *ᵥ y) := by
    rw [pm, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [e]
  exact add_mem hy (smul_Lf I hI (K_sub_mv I hx hy))

theorem mkG_K {u : I.E ⊗[I.F] Af I.F} (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u)
    (hI : u ∈ IntAf I.F I.E) {x : I.Gf} (hx : x ∈ I.Kset) : mkG I u hu hσ x ∈ I.Kset := by
  intro y
  show y ∈ I.Lf ↔ pm u (I.fmat x) *ᵥ y ∈ I.Lf
  refine ⟨fun hy => pm_mv_mem I hI hx hy, fun hy => ?_⟩
  have e : pm u (I.fmat x⁻¹) *ᵥ (pm u (I.fmat x) *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, pm_mul hu, fmat_inv_mul, pm_one, Matrix.one_mulVec]
  rw [← e]
  exact pm_mv_mem I hI (K_inv I hx) hy

theorem mkG_Kg {u : I.E ⊗[I.F] Af I.F} (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u)
    (hI : u ∈ IntAf I.F I.E) {m : ℕ} {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E)
    (huc : u = (m : I.E ⊗[I.F] Af I.F) * c) {x : I.Gf} (hx : x ∈ I.Kset) : mkG I u hu hσ x ∈ I.Kg m := by
  refine ⟨mkG_K I hu hσ hI hx, fun y hy => ⟨c • ((I.fmat x - 1) *ᵥ y), smul_Lf I hc (K_sub_mv I hx hy), ?_⟩⟩
  rw [fmat_mkG, pm_sub_one, Matrix.smul_mulVec, huc, mul_smul]

theorem kcrt_holds {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) : Formalism.L2.SG.AllRowsOf.KCRT I m₁ m₂ := by
  intro x hx
  obtain ⟨c₁, hc₁, e₁⟩ := compl_eq (F := I.F) m₁
  obtain ⟨c₂, hc₂, e₂⟩ := idem_eq (F := I.F) h
  set s : Af I.F := eT (Tm (F := I.F) m₁) with hs
  have hss : s * s = s := eT_idem _
  have hsI : s ∈ Formalism.UG.intAd I.F := eT_mem _
  have hu₁ : iA I (1 - s) * iA I (1 - s) = iA I (1 - s) := by
    rw [← map_mul]; congr 1; linear_combination hss
  have hu₂ : iA I s * iA I s = iA I s := by rw [← map_mul, hss]
  have hI₁ : iA I (1 - s) ∈ IntAf I.F I.E := iA_mem I (sub_mem (one_mem _) hsI)
  have hI₂ : iA I s ∈ IntAf I.F I.E := iA_mem I hsI
  have hC₁ : iA I (1 - s) = (m₁ : I.E ⊗[I.F] Af I.F) * iA I c₁ := by rw [e₁, map_mul, map_natCast]
  have hC₂ : iA I s = (m₂ : I.E ⊗[I.F] Af I.F) * iA I c₂ := by rw [e₂, map_mul, map_natCast]
  have h0 : iA I (1 - s) * iA I s = 0 := by rw [← map_mul, sub_mul, one_mul, hss, sub_self, map_zero]
  have h1 : iA I (1 - s) + iA I s = 1 := by rw [← map_add, sub_add_cancel, map_one]
  refine ⟨mkG I _ hu₁ (sig_iA I _) x, mkG_Kg I hu₁ (sig_iA I _) hI₁ (iA_mem I hc₁) hC₁ hx,
    mkG I _ hu₂ (sig_iA I _) x, mkG_Kg I hu₂ (sig_iA I _) hI₂ (iA_mem I hc₂) hC₂ hx, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  show I.fmat x = pm (iA I (1 - s)) (I.fmat x) * pm (iA I s) (I.fmat x)
  rw [pm_mul_compl h0 h1]

end Inst

end Formalism.L2.SG.Pf.AllRowsKCRT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRMul
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsRMul

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

abbrev phi (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ℂ := ⟪x, X.B.R (1, c) y⟫_ℂ

theorem R_facts :
    (∀ a b : X.B.I.GA, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ (∀ a F, ‖X.B.R a F‖ = ‖F‖) ∧
      (∀ x y : X.B.I.L2 X.B.μf X.B.fund, StronglyMeasurable (phi X x y)) := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hU := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have := hFR.2.1
  have := hFR.2.2.2.1
  have : X.B.μf.IsMulRightInvariant := hU
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := rr_muA_left X.B.I X.B.μf
  have : (X.B.I.muA X.B.μf).IsMulRightInvariant := rr_muA_right X.B.I X.B.μf
  have : SigmaFinite (X.B.I.muA X.B.μf) := rr_muA_sigmaFinite X.B.I X.B.μf
  have h1 := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have h2 := rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec
  refine ⟨fun a b => rr_mul h1 h2 a b, fun a F => rr_norm h1 h2 a F, fun x y => ?_⟩
  exact (rr_weak_meas h1 h2 x y).comp_measurable (measurable_const.prodMk measurable_id)

theorem phi_bound (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ‖phi X x y c‖ ≤ ‖x‖ * ‖y‖ := by
  have h := (R_facts X).2.1 (1, c) y
  calc ‖phi X x y c‖ ≤ ‖x‖ * ‖X.B.R (1, c) y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [h]

theorem isRConvF_conv {f g : X.B.I.Gf → ℂ} {T U : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (hf : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (hg : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R g U) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (X.B.I.convF X.B.μf f g) (T.comp U) := by
  obtain ⟨hmul, -, hmeas⟩ := R_facts X
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SecondCountableTopology X.B.I.Gf := rr_secondCountable X.B.I X.B.μf
  have hK : Integrable (fun p : X.B.I.Gf × X.B.I.Gf => f p.1 * g (p.1⁻¹ * p.2)) (X.B.μf.prod X.B.μf) := by
    have h0 : Integrable (fun q : X.B.I.Gf × X.B.I.Gf => f q.1 * g q.2) (X.B.μf.prod X.B.μf) := hf.1.mul_prod hg.1
    exact ((measurePreserving_prod_inv_mul X.B.μf X.B.μf).integrable_comp h0.aestronglyMeasurable).2 h0
  have hF : ∀ x y : X.B.I.L2 X.B.μf X.B.fund, Integrable (fun p : X.B.I.Gf × X.B.I.Gf =>
      f p.1 * g (p.1⁻¹ * p.2) * phi X x y p.2) (X.B.μf.prod X.B.μf) := fun x y =>
    hK.mul_bdd ((hmeas x y).comp_measurable measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => phi_bound X x y p.2)
  refine ⟨hK.integral_prod_right, fun x y => ?_⟩
  have step : ∀ a, ⟪x, X.B.R (1, a) (U y)⟫_ℂ = ∫ c, g (a⁻¹ * c) * phi X x y c ∂X.B.μf := by
    intro a
    rw [← ContinuousLinearMap.adjoint_inner_left, hg.2]
    have e : ∀ b, g b * ⟪ContinuousLinearMap.adjoint (X.B.R (1, a)) x, X.B.R (1, b) y⟫_ℂ =
        g b * phi X x y (a * b) := by
      intro b
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← hmul, Prod.mk_mul_mk, one_mul]
    simp_rw [e]
    rw [← integral_mul_left_eq_self (fun c => g (a⁻¹ * c) * phi X x y c) a]
    congr 1
    funext b
    simp only [inv_mul_cancel_left]
  rw [ContinuousLinearMap.comp_apply, hf.2]
  simp_rw [step, ← integral_const_mul]
  have hF' : Integrable (Function.uncurry fun a c => f a * (g (a⁻¹ * c) * phi X x y c)) (X.B.μf.prod X.B.μf) := by
    have := hF x y
    simp only [mul_assoc] at this
    exact this
  rw [integral_integral_swap hF']
  congr 1
  funext c
  unfold AutInst.convF
  rw [← integral_mul_const]
  congr 1
  funext a
  ring

end Formalism.L2.SG.Pf.AllRowsRMul
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem wuBesselOfLoc_all {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : WuBesselOfLoc C :=
  Formalism.L2.SG.Pf.WuBL.wuBesselOfLoc Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis C

theorem goodSRest_of_loc {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ :=
  Formalism.L2.SG.Pf.GoodS.goodSRest_of hB u u' τ hsm (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ)
    (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ) hT

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoEqv
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.S
open Formalism.MainNotions.StandardLattice Matrix
open scoped InnerProductSpace ComplexConjugate ENNReal TensorProduct

namespace Formalism.L2.SG.EvalTOntoEqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.EvalTOntoExt Formalism.L2.SG.EvalTOntoPsi Classical

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)}
  {μ : Measure (GA D (D.sp.Y 0))} {c : ℝ} {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S}
  {U : ∀ v, X.B.H v ≃ₗᵢ⋆[ℂ] M.H (X.pl v)} {Φ : X.B.Hs →L[ℂ] L2X X}

def single (v' : NumberField.InfinitePlace X.B.I.F) (m : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hm : m ∈ UJset (X.B.I.ε v')) : X.B.I.Ginf :=
  Function.update 1 v' ⟨(Formalism.IndefR.SchurOrthogonalityAlt.isUnit_of_mem_UJ (X.B.I.ε v') hm).unit, hm⟩

end Formalism.L2.SG.EvalTOntoEqv

end
end

