import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentLevelNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPow
section
noncomputable section

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem pi_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem glint_entry {n : ℕ} {h : GL (Fin n) L} (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (r s : Fin n) :
    (h : Matrix (Fin n) (Fin n) L) r s ∈ Formalism.UG.intL L := by
  obtain ⟨g0, hg0⟩ := hh
  rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) r s).2

theorem mulVec_int {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : (M *ᵥ v) r ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun s _ => (Formalism.UG.intL L).mul_mem (hM r s) (hv s)

theorem dvdPow_mulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, DvdPow ϖ k (M r s))
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]; exact dvdPow_mul_int (hM r s) (hv s)

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (h : Formalism.UG.UJ σ J) (x y : Fin n → L) :
    Formalism.UG.hform σ J (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
      (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hu : Formalism.UG.cT σ ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J := h.2
  rw [hform_eq_dot, hform_eq_dot]
  set H := ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have e1 : (fun i => σ ((H *ᵥ x) i)) = (H.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; exact RingHom.map_mulVec σ H x i
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  exact congrArg (· *ᵥ y) hu

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_intMulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, DvdPow ϖ k (v r)) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  exact dvdPow_sum _ _ fun s _ => dvdPow_mul_int (hv s) (hM r s)

theorem indepMod_mulVec {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {h : GL (Fin n) L}
    (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) {z : ι → Fin n → L} (hz : IndepMod ϖ z) :
    IndepMod ϖ (fun i => (h : Matrix (Fin n) (Fin n) L) *ᵥ z i) := by
  intro d hd hs i
  refine hz d hd (fun r => ?_) i
  set w : Fin n → L := ∑ j, d j • z j with hw
  have e1 : ∀ s, ((h : Matrix (Fin n) (Fin n) L) *ᵥ w) s = ∑ j, d j * ((h : Matrix (Fin n) (Fin n) L) *ᵥ z j) s := by
    intro s
    simp [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
  have e2 : ∑ j, d j * z j r = (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ ((h : Matrix (Fin n) (Fin n) L) *ᵥ w)) r := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp [hw, Finset.sum_apply]
  rw [e2]
  exact dvdPow_intMulVec (glint_entry ((Formalism.UG.GLint _ _).inv_mem hh)) (fun s => by rw [e1]; exact hs s) r

theorem indepMod_sub {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {z : ι → Fin n → L} (hz : IndepMod ϖ z)
    (p : ι → Prop) [DecidablePred p] : IndepMod ϖ (fun i : {i // p i} => z i.1) := by
  intro d hd hs i
  let d' : ι → L := fun j => if hj : p j then d ⟨j, hj⟩ else 0
  have h1 : ∀ j, d' j ∈ Formalism.UG.intL L := by
    intro j; by_cases hj : p j
    · simp only [d', dif_pos hj]; exact hd _
    · simp only [d', dif_neg hj]; exact (Formalism.UG.intL L).zero_mem
  have h2 : ∀ r, ∑ j, d' j * z j r = ∑ j : {i // p i}, d j * z j.1 r := by
    intro r
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => d' j * z j r)]
    have a1 : ∑ j : {i // ¬ p i}, d' j.1 * z j.1 r = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [d', dif_neg j.2]
    rw [a1, add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp [d', dif_pos j.2]
  have := hz d' h1 (fun r => by rw [h2]; exact hs r) i.1
  simpa [d', dif_pos i.2] using this

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

theorem witt_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJT hJh ι _ a z z' ha hz hz' hiz hiz' hG
  classical
  have hϖ := pi_int hU
  have key : ∀ k, 1 ≤ k → ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
      (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, DvdPow ϖ (min (a i) k) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h, hh, hc⟩ := GlobalTheory.T.integral_witt_unitary_mod_uniformizer L ϖ σ q hU hq n' JT hJT hJh ι z z' hz hz' hiz hiz'
        (fun i j => dvdPow_mono hϖ (le_min (ha i) (ha j)) (hG i j))
      refine ⟨h, hh, fun i r => ?_⟩
      rw [min_eq_right (ha i)]; exact hc i r
    | succ k hk ih =>
      obtain ⟨h, hh, hc⟩ := ih
      have hHint := glint_entry hh
      obtain ⟨g, hg, hg1, hgc⟩ := GlobalTheory.T.unitaryGroup_hensel_step_families L ϖ σ q hU hq n' JT hJT hJh {i // k < a i}
        (fun i => ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i.1) (fun i => z' i.1) k hk
        (fun i r => mulVec_int hHint (hz i.1) r) (fun i r => hz' i.1 r)
        (indepMod_sub (indepMod_mulVec hh hiz) (fun i => k < a i))
        (fun i r => by
          have h0 := hc i.1 r
          rw [min_eq_right i.2.le] at h0
          have h1 := dvdPow_neg h0
          rwa [neg_sub] at h1)
        (fun i j => by
          simp only [hform_unitary]
          exact dvdPow_mono hϖ (le_min i.2 j.2) (hG i.1 j.1))
      refine ⟨g * h, (Formalism.UG.GLint _ _).mul_mem hg hh, fun i r => ?_⟩
      have e : (((g * h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i
          = ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) := by
        simp [Matrix.mulVec_mulVec]
      rw [e]
      by_cases hki : k < a i
      · rw [min_eq_right (Nat.succ_le_of_lt hki)]
        exact hgc ⟨i, hki⟩ r
      · push_neg at hki
        rw [min_eq_left (by omega)]
        have h2 := hc i r
        rw [min_eq_left hki] at h2
        have h1 : DvdPow ϖ (a i) (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
            (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r) :=
          dvdPow_mono hϖ hki (dvdPow_mulVec (fun r s => by simpa [Matrix.sub_apply] using hg1 r s)
            (mulVec_int hHint (hz i)) r)
        have e2 : (((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r - z' i r
            = (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
              (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r)
              + ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
        rw [e2]; exact dvdPow_add h1 h2
  obtain ⟨h, hh, hc⟩ := key (1 + ∑ i, a i) (by omega)
  refine ⟨h, hh, fun i r => ?_⟩
  have h0 := hc i r
  have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  rwa [min_eq_left (by omega)] at h0

end GlobalTheory.Hk3.IntWittMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem intOff_pow' {S : Finset ℕ} {z : ℂ} (h : IntOff S z) (n : ℕ) : IntOff S (z ^ n) := by
  induction n with
  | zero => simpa using IntOff.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem intOff_prod' {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) :=
  Finset.prod_induction _ (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem intAt_chArg_of_omPhi {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    {y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))}
    (h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y ≠ 0) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
  have hm := hL.hm
  by_cases hP : P.1 ∈ Pr.vGs
  · have h1 := (GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type Ch sel mu cst i P (by omega) hP _ _ (hL.stabG i al P hP)
      (hL.stabG (i + 1) be P hP)).2 y h0
    rw [hL.depthG P hP, pow_one, mul_neg]
    exact GlobalTheory.TopStep.intAt_neg h1
  · have h1 := right_ne_zero_of_mul h0
    rw [PhiAt, if_neg hP] at h1
    have hb := hL.boundQ i al P hP
    have hb' := hL.boundQ (i + 1) be P hP
    have hD := hL.depthQ' P hP
    simp only [lamYat, hP, if_false, GlobalTheory.GO.ChRoot.mem_lamY_zero] at hb hb'
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
      refine GlobalTheory.ColPeriod.EntQ.intAt_chArg _ y fun v hv => ?_
      have h2 := (hb' _ (GlobalTheory.ColPeriod.EntQ.int_of_PhiQ (GlobalTheory.ColPeriod.EntQ.k_le_N R _) (GlobalTheory.ColPeriod.EntQ.k_le_N R _) h1 (hb v hv).1)).2
      have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
      simpa [h3] using h2
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact GlobalTheory.TopStep.intAt_neg ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul hint)

theorem intOff_xiEntry : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hg i hi al be p p' x
  have hL := t.idx_ok μ
  have hm := hL.hm
  unfold XiEntry
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod' _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using IntOff.one
    · simpa using IntOff.zero
  · have hq := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
    have hst : P.1 ∈ t.Pr.vGs → (t.idx μ).h i al P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧
        (t.idx μ).h (i + 1) be P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1) :=
      fun hP => ⟨hL.stabG i al P hP, hL.stabG (i + 1) be P hP⟩

    have hom : ∀ y, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P
        ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y)) := fun y =>
      GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t hmu hval u μ hg i (by omega) P _ _ hst y
    unfold XiAt E1at Loc.E1
    rw [map_mul, map_mul, map_sum]
    refine IntOff.mul (GlobalTheory.UnipVol.intOff_volN_Cbe D L hT Gi Gl K Y cX ex t u μ i P _) (IntOff.mul ?_ (IntOff.sum _ _ fun s _ => ?_))
    · rw [map_pow, map_inv₀, map_pow, map_natCast, ← inv_pow]
      exact intOff_pow' (intOff_pow' (IntOff.inv_nat hq) _) _
    · generalize Loc.xx1 _ s = y
      by_cases h0 : omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y = 0
      · rw [h0, zero_mul, map_zero]
        exact IntOff.zero
      · rw [map_mul]
        refine (hom _).mul (IntOff.of_pow (n := qOf P.1 ^ (t.cst μ).D P) (pow_pos (GlobalTheory.GO.ChRoot.qOf_pos _) _) ?_)
        rw [← map_pow, GlobalTheory.GO.ChRoot.psi_root hL.cst_ok P _ (intAt_chArg_of_omPhi hL hi al be P h0), map_one]

end GlobalTheory.KerTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRepOfIsAssoc
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.CarUniq

theorem isTheRep_of_isAssoc : LocalLanglandsExists → RecUnique → AutomorphicFormsFiniteGL → IrreducibleAdmissibleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (R : G E Ω →* GL (Fin a) (Qbar l)), GlobalTheory.CarHyp.IsAssoc π ι R → GlobalTheory.CarHyp.IsTheRep π ι R := by
  intro hLL hU hAF hIA E Ω _ _ _ _ _ _ l _ ι a π R hR
  refine ⟨hR, fun R' hR' => ?_⟩
  refine GlobalTheory.TraceConjCofinite.main E Ω l a R R' hR.cont hR'.cont hR.ss hR'.ss ?_
  have hl : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_)
    exact Ideal.dvd_span_singleton.2 (not_not.1 hv)
  filter_upwards [GlobalTheory.CuspRep.LocSph.locComp_spherical E a π, hl] with w hw hlw A h σ
  obtain ⟨rc, hrc⟩ := hLL E Ω A w h
  have hrc' := hU.isTheRec hrc
  obtain ⟨s, hs, had⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF E a π w
  obtain ⟨v, h0, hv⟩ := hw s hs
  have hsp : SmGL.IsSpherical s.ρ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩
    obtain ⟨x, hx⟩ := x
    rw [SmGL.SphCompletion.KO_completion] at hx
    obtain ⟨g, rfl⟩ := hx
    exact (hv g).trans (one_smul _ _).symm
  have hirr := (GlobalTheory.ContraRefl.contra_irreducible_reflexive _ (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _
    s.ρ s.ρ had had).1 s.irred
  let s' : SmIrr (GL (Fin a) (w.adicCompletion E)) :=
    { V := _, ρ := SmGL.contra s.ρ, smooth := SmGL.isSmooth_contra _, irred := hirr }
  have e : Nonempty (s'.ρ.Equiv (SmGL.contra s.ρ)) := ⟨.refl _⟩
  have h1 := hR.unr w hlw A h rc hrc' s s' hs hsp e
  have h2 := hR'.unr w hlw A h rc hrc' s s' hs hsp e
  have hx := isWDOf_wdOf (h := h) hlw ι (Units.continuous_val.comp hR.cont)
  have hx' := isWDOf_wdOf (h := h) hlw ι (Units.continuous_val.comp hR'.cont)
  rw [h1] at hx
  rw [h2] at hx'
  exact GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι a R R' w A h _ hx hx' σ

end GlobalTheory.CarUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionsCommonLinearOperatorOffSplitPrime
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

namespace GlobalTheory.KerCommon

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := GlobalTheory.T.exists_common_scale_lattice_pairs_split_prime

theorem perO_scale : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (N₁ N₂ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (w : 𝓞 E), (∀ y ∈ N₂, w • y ∈ N₁) → (∀ y ∈ N₁', w • y ∈ N₂') → ∀ x ∈ perO AA0 N₁ N₁', (w * w) • x ∈ perO AA0 N₂ N₂' := by
  intro E _ _ _ a b AA0 N₁ N₂ N₁' N₂' w h2 h1 x hx
  unfold perO at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨r, hr, (w * w) • y, ?_, ?_⟩
    · intro v hv
      have h3 := h1 _ (hy _ (h2 v hv))
      have e : ((w * w) • y) v = w • y (w • v) := by
        rw [LinearMap.smul_apply, mul_smul, LinearMap.map_smul_of_tower]
      rw [e]
      exact h3
    · rw [smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o z _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

theorem common_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := GlobalTheory.T.common_representatives_period_lattice_halves

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

theorem unimod_iff {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E n)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      Submodule.mem_one, RingHom.mem_range]
    rfl
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  constructor
  · intro h y
    rw [← hm y, h]
  · intro h
    ext y
    rw [hm y]
    exact (h y).symm

theorem admissible_pair_twist {D : D7} {a b : ℕ} (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (h01 : ∀ Q, ex Q = 1 ∨ ex Q = 0 ∨ ex Q = -1) (hc : ∀ Q, ex (Formalism.L2.Col.conjPrime₂ Q) = -ex Q) :
    TaylorLogMetric.admitted D a b N (twist₂ N' cl ex) := by
  have hl := hh_tw_lattice N' ⟨hA.2.2.2.1, hA.2.2.2.2.1⟩ hcl ex h01
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hl.span_eq_top,
    (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩

theorem split_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl)
    (hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) :
    SplitHyp (hK D cc δ a b) (alK D cc δ a b) (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (lamK cc δ N N') := by
  have := tau_nonempty D
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := expS_cases SS
  have he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1
    omega
  have hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q := by
    intro Q
    show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q
    rw [hconj1 Q]
  exact half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl
    (KS.Lat.delta_ne hcc hδ) hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA)
    (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he1 hconj1)) (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he2 hconj2))

theorem finIdx_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) : FinIdx cc δ SS cl N N' :=
  finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl
    (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))

theorem eNat_fixed_of_vec {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hV : B.VecP χ) {a b : ℕ}
    {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} (hA : TaylorLogMetric.admitted D a b N N') :
    B.eNat χ a b N N' ∈ fixedBy (hK D cc δ a b) (alK D cc δ a b) (lamK cc δ N N') := by
  have hm := (hV a b N N' hA).1
  intro x hx z
  have hx' : x ∈ TaylorLogMetric.La D B.tor N N' := by rw [← lamK_eq cc δ N N']; exact hx
  have h1 := hm.2 x hx' z
  rw [U_eq_opU] at h1
  have hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x := by
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx']
    unfold alK alV
    rw [HV_eq_formV]
  rw [hal]
  exact h1

theorem locP_eq_of_scale {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]
    (M M₀ : Submodule (𝓞 E) W) (g : 𝓞 E) (Q : HeightOneSpectrum (𝓞 E)) (hg : g ∉ Q.asIdeal)
    (h1 : ∀ x ∈ M, g • x ∈ M₀) (h2 : ∀ x ∈ M₀, g • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₀ := by
  have hg' : g ∈ Q.asIdeal.primeCompl := hg
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h2 _ hx⟩

theorem kerTh_common_op : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  intro D cc δ B χ hcc hδ hδ0 _hL hV SS cl hcl hSS a b P _hP hPS hPS' hcP _hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN
  have := tau_nonempty D
  obtain ⟨g, ⟨k, hk⟩, hgQ, hg⟩ := exists_scale D P SS cl hPS hPS' hcP ι a b N N₀ N' N₀' fun i => (hN i).2
  have hsc : ∀ i, (∀ x ∈ perO (aaOf D cc) (N i) (N' i), (g * g) • x ∈ perO (aaOf D cc) N₀ N₀') ∧
      ∀ x ∈ perO (aaOf D cc) N₀ N₀', (g * g) • x ∈ perO (aaOf D cc) (N i) (N' i) := fun i =>
    ⟨perO_scale D.host.E a b (aaOf D cc) (N i) N₀ (N' i) N₀' g (hg i).1.2 (hg i).2.1,
      perO_scale D.host.E a b (aaOf D cc) N₀ (N i) N₀' (N' i) g (hg i).1.1 (hg i).2.2⟩
  have hI0 := finIdx_of_adm (cc := cc) (δ := δ) SS cl N₀ N₀' hA0 hcl
  obtain ⟨SX, SA, SB, hR⟩ := common_reps D.host.E D.what₂.Tau ι a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS cl N₀ N₀' N N' (g * g) hδ0
    ⟨k + k + (cl : 𝓞 D.host.E) * k * k, by rw [hk]; ring⟩ hsc hI0.1 hI0.2.1 hI0.2.2
  have hxi0 : ∀ z, xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 z = 0 := by
    intro z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 0 z).2.2.2
    have e : (fun v : TaylorLogMetric.VC D a b => (1 : ℂ) * (0 : TaylorLogMetric.VC D a b → ℂ) v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = 0 := by
      funext v; simp
    rw [e, one_mul] at h
    linear_combination -h
  refine ⟨{ toFun := fun θ => xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) θ,
            map_add' := ?_, map_smul' := ?_ }, fun i => ?_⟩
  · intro x y
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x y z).2.2.2
    have e : (fun v => (1 : ℂ) * x v + y v) = x + y := by funext v; simp
    rw [e, one_mul] at h
    simpa using h
  · intro c x
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB c (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x 0 z).2.2.2
    have e : (fun v => c * x v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = c • x := by funext v; simp
    rw [e, hxi0, add_zero] at h
    simpa using h
  · obtain ⟨hAi, -, -⟩ := hN i
    have hyp := split_of_adm B SS cl (N i) (N' i) hcc hδ hAi hcl hSS
    have hIi := finIdx_of_adm (cc := cc) (δ := δ) SS cl (N i) (N' i) hAi hcl
    have hθ := eNat_fixed_of_vec B χ hcc hδ hV hAi
    have hg2 : ∀ Q ∈ SS, g * g ∉ Q.asIdeal := fun Q hQ h =>
      (Q.isPrime.mem_or_mem h).elim (hgQ Q hQ) (hgQ Q hQ)
    have hDi : DatLoc D cc SS cl (N i) (N' i) Ξ :=
      hD.of_locP_eq fun Q hQ => locP_eq_of_scale _ _ (g * g) Q (hg2 Q hQ) (hsc i).1 (hsc i).2
    have hinv := hDi.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
    funext z
    exact twist_representatives _ (hK D cc δ a b) (alK D cc δ a b) _ _ _ hyp SX SA SB _ _ _ (hR i).1 (hR i).2.1 (hR i).2.2
      (repsOf_spec _ _ hIi.1) (repsOf_spec _ _ hIi.2.1) (repsOf_spec _ _ hIi.2.2) 1 _ hθ _ hinv z

end GlobalTheory.KerCommon
end
end

