import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.Columns.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TwistCong

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem sclLat_zero (q N : ℕ) : LocE.sclLat P q N (fun _ => 0) = stdAt E N P := by
  ext x
  rw [CongLevel.mem_sclLat, mem_stdAt]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P := by
  have e : LocE.scE n 0 = fun _ => (0 : ℤ) := by
    funext l
    unfold LocE.scE
    split_ifs <;> simp
  unfold LocE.lamY
  rw [e, sclLat_zero]

theorem inX_mem_std {n : ℕ} (c : ℕ) {x : Sp E n} (hx : x ∈ stdAt E n P) : Loc.inX E n c x ∈ stdAt E (n + c) P := by
  refine mem_stdAt.2 fun l => ?_
  rw [CongLevel.inX_apply]
  split_ifs
  · exact mem_stdAt.1 hx _
  · exact intAt_zero

theorem resX_mem_std {n : ℕ} (c : ℕ) {v : Sp E (n + c)} (hv : v ∈ stdAt E (n + c) P) :
    CongLevel.resX c v ∈ stdAt E n P :=
  mem_stdAt.2 fun i => mem_stdAt.1 hv (Fin.castAdd c i)

theorem stab_of_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P)
    (hg' : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) : g ∈ stabL E N (stdAt E N P) := by
  have hq := qOf_ne_zero (P := P)
  have maps : ∀ f : Sp E N ≃ₗ[E] Sp E N, (∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (f x - x) ∈ stdAt E N P) →
      ∀ x ∈ stdAt E N P, f x ∈ stdAt E N P := by
    intro f hf x hx
    have e : f x = x + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (f x - x)) := by
      rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
    rw [e]
    exact add_mem hx (smul_mem_locP (intAt_nat _) (hf x hx))
  intro x
  refine ⟨fun hx => ?_, maps g hg x⟩
  have := maps g⁻¹ hg' _ hx
  rwa [show g⁻¹ (g x) = x from LinearEquiv.symm_apply_apply _ x] at this

theorem conj_extE_cong {n c : ℕ} (j D : ℕ) (hjD : j + 1 ≤ D) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hb : ∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ (((qOf P : ℕ) : E) ^ j) • h x ∈ stdAt E (n + c) P)
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : ∀ y ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ D)⁻¹ • (κ y - y) ∈ stdAt E n P) :
    ∀ x ∈ stdAt E (n + c) P, ((qOf P : ℕ) : E)⁻¹ • ((h⁻¹ * CongLevel.extE c κ * h) x - x) ∈ stdAt E (n + c) P := by
  intro x hx
  have hq := qOf_ne_zero (P := P)
  set q : E := ((qOf P : ℕ) : E) with hqdef
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjD
  have hy := (hb x hx).2
  set y := q ^ j • h x with hydef
  have hhx : h x = (q ^ j)⁻¹ • y := by
    rw [hydef, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hq), one_smul]
  have hres := resX_mem_std c hy
  have hk := hκ _ hres
  have e1 : (h⁻¹ * CongLevel.extE c κ * h) x - x = h⁻¹ (CongLevel.extE c κ (h x) - h x) := by
    rw [map_sub]
    show h.symm (CongLevel.extE c κ (h x)) - x = h.symm (CongLevel.extE c κ (h x)) - h.symm (h x)
    rw [LinearEquiv.symm_apply_apply]
  have e2 : CongLevel.extE c κ (h x) - h x =
      Loc.inX E n c ((q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [CongLevel.extE_apply, add_sub_cancel_left, hhx, map_smul, map_smul, smul_sub]
  have e3 : q⁻¹ • (q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y) =
      q ^ d • ((q ^ (j + 1 + d))⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
    ring
  rw [e1, e2, ← map_smul, ← map_smul, e3]
  refine (hb _ (inX_mem_std c ?_)).1
  exact smul_mem_locP (intAt_pow (intAt_nat _) d) hk

theorem entry_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P) (l i : ℕ) (hl : l < N) (hi : i < N) :
    IntAt P (Loc.atN (g (Loc.eN E N l)) i) ∧ redP P (Loc.atN (g (Loc.eN E N l)) i) = if i = l then 1 else 0 := by
  have hq := qOf_ne_zero (P := P)
  have he : Loc.eN E N l ∈ stdAt E N P := mem_stdAt.2 fun m => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hy := mem_stdAt.1 (hg _ he) ⟨i, hi⟩
  have e : g (Loc.eN E N l) = Loc.eN E N l + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) := by
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
  have ee : Loc.atN (g (Loc.eN E N l)) i = (if i = l then (1 : E) else 0) +
      ((qOf P : ℕ) : E) * (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) ⟨i, hi⟩ := by
    conv_lhs => rw [e]
    unfold Loc.atN
    rw [dif_pos hi]
    simp [Loc.eN]
  have h1 : IntAt P (if i = l then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have h2 := (intAt_nat (P := P) (qOf P)).mul hy
  rw [ee]
  refine ⟨h1.add h2, ?_⟩
  rw [reduction_add h1 h2, reduction_mul (intAt_nat _) hy, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Lat

open GlobalTheory.TopStep in

theorem cong_mem_prCat_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P hP C hC
  have hq := qOf_ne_zero (P := P.1)
  have hstd : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E (R.N j + cOf R j) P.1 := by
    unfold lamYat
    rw [if_neg hP]
    exact lamY_zero _ _ _
  have hD : j + 1 ≤ cst.D P := by
    have h1 := hL.depthQ' P hP
    have h2 := hL.hm
    omega
  have hb : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
      (((qOf P.1 : ℕ) : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    intro x hx
    rw [← hstd] at hx ⊢
    exact hL.boundQ j b P hP x hx
  have hκ : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1 y - y) ∈ stdAt X.E (R.N j) P.1 :=
    mem_prinCong.1 hC
  have hκ' : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1⁻¹ y - y) ∈ stdAt X.E (R.N j) P.1 :=
by
    intro y hy
    have h0 := mem_prinCong.1 (inv_mem hC) y hy
    rwa [Subgroup.coe_inv] at h0
  have hg := conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1 hκ
  have hg' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, ((qOf P.1 : ℕ) : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ x - x) ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    have e : ((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1⁻¹ * L.h j b P := by
      rw [← CongLevel.extE_inv]
      group
    rw [e]
    exact conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1⁻¹ hκ'
  have hs := stab_of_cong _ hg hg'
  refine ⟨CongLevel.extE (cOf R j) C.1, ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ C.1, ?_⟩, CongLevel.extE_inX _ C.1, ?_⟩
  · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P := by simp
    show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) ∈ Jat (Pr := Pr) cst.sharp j P.1
    rw [e]
    unfold Jat
    rw [if_neg hP]
    refine ⟨hs, ?_⟩
    have ep : LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) =
        LocE.sclLat P.1 (qOf P.1) (R.N j + cOf R j)
          (fun l => (fun _ => (0 : ℤ)) l + if R.k + j ≤ l ∧ l < R.N j then 1 else 0) := by
      unfold LocE.parL
      congr 1
      funext l
      simp
    have hM : ∀ _s : ℕ, LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) ≤ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro _
      rw [ep, ← sclLat_zero (P := P.1) (qOf P.1)]
      exact CongLevel.sclLat_le P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j)
    have hM' : ∀ (_s : ℕ) (x : Sp X.E (R.N j + cOf R j)), ((qOf P.1 : ℕ) : X.E)⁻¹ • x ∈ stdAt X.E (R.N j + cOf R j) P.1 →
        x ∈ LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
      intro _ x hx
      rw [ep]
      rw [← sclLat_zero (P := P.1) (qOf P.1)] at hx
      exact CongLevel.smul_mem_sclLat P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j) x hx
    exact (CongLevel.mem_flagU (qOf P.1) (stdAt X.E (R.N j + cOf R j) P.1)
      (fun _ => LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j)) (fun _ => 0) 0 Set.univ hM hM'
      (fun _ => zero_mem _) _ hs hg).1 0 trivial
  · unfold chiInv
    have hn : Loc.n1Arg (CongLevel.extE (cOf R j) C.1) = 0 := by
      unfold Loc.n1Arg
      refine Finset.sum_eq_zero fun i _ => ?_
      have e : CongLevel.extE (cOf R j) C.1 (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) =
          Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1) := by
        rw [show R.N j + i + 1 = R.N j + (i + 1) by ring, CongLevel.extE_apply, CongLevel.resX_eN]
        simp
      rw [e]
      unfold Loc.atN
      split_ifs with h1
      · simp [Loc.eN]
      · rfl
    rw [hn, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul]
    unfold lamRow
    rw [if_neg hP]
    unfold LocE.lamQB
    rw [GlobalTheory.LamRowCong.unitV_det_eq_one, inv_one]
    · intro s t
      have := s.2
      have := t.2
      exact (entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).1
    · ext s t
      have := s.2
      have := t.2
      rw [Matrix.map_apply, Matrix.one_apply]
      show redP P.1 (Loc.atN (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)
        (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1)) = _
      rw [(entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).2]
      by_cases hst : s = t
      · subst hst
        simp
      · rw [if_neg (fun e => hst (Fin.ext (by omega))), if_neg hst]

end GlobalTheory.TwistCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat GlobalTheory.Mem.Df GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.AtG.RX

section Fam
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (R3.Gc X.B px → X.B.LL))
  (tr : R3.TrI X.B px) (a : I.ι)

set_option maxHeartbeats 1000000 in

theorem isFormOf_exists (z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    ∃ y, IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) := by
  have hK := mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX
  obtain ⟨hφ, -⟩ := (mem_MtildeV_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) z.1).1 z.2
  let F : (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).EqFun := ⟨z.1, hφ⟩
  have h1 := (mem_lvlPartX_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hK F).2 z.2
  rw [← LiftForms.range_lvlE] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, F, z.2, ?_, rfl⟩
  apply heq_of_eq
  show _ = (MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm
    ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).lvlE _ _ _ *ᵥ y)
  rw [Matrix.mulVecLin_apply] at hy
  rw [hy]
  exact ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm_apply_apply _).symm

theorem isFormOf_unique {y} {z z' : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y))
    (h' : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z'
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) : z = z' := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  obtain ⟨F', hF', e2, rfl⟩ := h'
  have e3 := eq_of_heq (e1.trans e2.symm)
  have e4 := ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).res _).injective e3
  subst e4
  rfl

set_option maxHeartbeats 1000000 in

theorem isFormOf_mem_iff {y} {z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) :
    y ∈ rNab X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) ↔
      z ∈ MtildeL (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  have e2 := eq_of_heq e1
  refine (LiftForms.mem_lvlNab _ _ _ _ y).trans ?_
  show R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y ∈ intForms _ ↔ _
  rw [← e2]
  exact (GSD.mem_intNab_iff _ (mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX) _ F).symm

end Fam

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}

theorem lat_of_rx (x : RXs t) (a : w.C.Tup) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, x.e a (toCx w.I t.hX a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      x.e a (toCx w.I t.hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  classical
  obtain ⟨hg, hiff⟩ := x.all.latA a
  have hc := x.crd a
  refine ⟨fun v hv => ?_, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hg v hv
    obtain ⟨z, -, hz⟩ := hc y
    exact ⟨z, hz.symm⟩
  · obtain ⟨y, hy⟩ := isFormOf_exists (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a z
    obtain ⟨z', hz', hj⟩ := hc y
    have e := isFormOf_unique (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy hz'
    obtain ⟨c, hc'⟩ := (hiff y).1 ((isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy).2 hz)
    exact ⟨c, by rw [e, ← hj]; exact hc'⟩
  · rintro ⟨c, hc'⟩
    choose! g hgy using hg
    let n := rDim (w.st Z).toD7 (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a)
    let y : Fin n → B.LL := ∑ v ∈ (Z.W.Mtilde a).gen, ((c v : 𝓞 B.LL) : B.LL) • @id (Fin n → B.LL) (g v)
    have hjy : x.all.jA a y = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
      let J : (Fin n → B.LL) →ₛₗ[B.embLL] Z.W.Amb a := x.all.jA a
      refine (map_sum J _ _).trans (Finset.sum_congr rfl fun v hv => ?_)
      exact (J.map_smulₛₗ _ _).trans (congrArg _ (hgy v hv))
    obtain ⟨z', hz', hj⟩ := hc y
    have e : z' = z := by
      apply toMtilde_injective (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) B.embLL
      apply (x.e a).injective
      exact hj.symm.trans (hjy.trans hc'.symm)
    rw [← e]
    exact (isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hz').1 ((hiff y).2 ⟨c, hjy⟩)

section Core

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (hX : B.fields.Ok)

theorem eq_rowForm' (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (G : (I.per l u a).Mt)
    (hG : SameForm I l u a (toCx I hX a z) G) : G = rowForm I l h u a z :=
  Subtype.ext (funext fun _ => funext fun p => hG p)

theorem rowPin_core (Z : TC.Later B (I.cols l)) (e0 : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (u : B.Word) (a : (I.cols l).Tup) (e : (I.per l u a).Mt ≃ₗ[ℂ] Z.W.Amb a)
    (he : ∀ F, SameForm I l u a F (e.symm (e0 a F)))
    (hgen : ∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e0 a (toCx I hX a z) = v)
    (hlat : ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e0 a (toCx I hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e (rowForm I l h u a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  have key : ∀ z, e (rowForm I l h u a z) = e0 a (toCx I hX a z) := fun z => by
    rw [← eq_rowForm' I h l hX u a z _ (he _)]
    exact e.apply_symm_apply _
  refine ⟨fun v hv => ?_, fun z => ?_⟩
  · obtain ⟨x, hx⟩ := hgen v hv
    exact ⟨x, (key x).trans hx⟩
  · rw [key]
    exact hlat z

end Core

theorem rowPin_of_rx : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  intro K B f T w Z Wt p0 t x a u
  obtain ⟨hg, hl⟩ := lat_of_rx (t := t) x a
  by_cases ha : a = (w.D Z).what₂.mu0
  · subst ha
    exact ⟨Z.W.eMt0 u, fun _ => HEq.rfl, fun hn => absurd rfl hn,
      rowPin_core w.I w.ok w.l t.hX Z x.e u _ (Z.W.eMt0 u) (x.eMt0 u) hg hl⟩
  · exact ⟨Z.W.eMtTw u a, fun hn => absurd hn ha, fun _ => rfl,
      rowPin_core w.I w.ok w.l t.hX Z x.e u a (Z.W.eMtTw u a) (x.eMtTw u a) hg hl⟩

end GlobalTheory.AtG.RX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFiel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

theorem rho_jet_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  classical
  intro B X I h hP l Z hJ u a i hi c c' e he
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I h hP l Z a u i hi
  set p := (I.stp u a i).rep c
  set p' := (I.stp u a (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hX hPr
    h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb a u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hN.1 hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb a u) N N' cA cB hN.1 hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u a i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb a u) N N')).comap (divLat cA (homAt (I.Sb a u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb a u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb a u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl, jetC_sum _ _ _ hs]
  have hr := rhoIs I h a u hi c.1 p c'.1 p'
  rw [show I.rho u a i c.1 p * I.rho' u a i c'.1 p' = _ from hr]
  have hσ : (ColIn.A I).σ₀ = B.embLL := rfl
  rw [hσ]
  apply RingHom.mem_fieldRange.1
  rw [mul_assoc, Finset.mul_sum]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) (Subfield.sum_mem _ fun q _ => ?_)
  obtain ⟨y, hy⟩ := hJ.exists_eq (a := a) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := e) hi
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ he
  rw [mul_left_comm]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
  exact ⟨y, hy⟩

end GlobalTheory.Mem.Col2.TC
end

