import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharacterIntegralFramePowEqOne
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead

variable {D : D7}

theorem det_mem_intAf {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

def finHom (D : D7) : AE D →* Formalism.MainNotions.StandardLatticesGL3.AE D :=
  ((GlobalTheory.BotFormula.toAfE D).symm.toRingHom.comp (finPart D)).toMonoidHom

theorem isFinIdl_map (x : (AE D)ˣ) (h : infPart D (x : AE D) = 1) : IsFinIdl x (Units.map (finHom D) x) := by
  refine ⟨h, ?_⟩
  change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))
  rw [← GlobalTheory.BotClassDict.finAdEquiv_toAfE, RingEquiv.apply_symm_apply]

theorem intU_map (x : (AE D)ˣ) (h : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IntU D (Units.map (finHom D) x) := by
  refine ⟨(GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_, (GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_⟩
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h'

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem exists_pow_cong (u : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) (hu : IntU D u) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D, ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  have hpow : ∀ k : ℕ, ((u : Formalism.MainNotions.StandardLatticesGL3.AE D)) ^ k ∈ OhE D := fun k => pow_mem hu.1 k
  choose b w hw hb using fun k => GlobalTheory.CongApprox.exists_int_approx D N hN _ (hpow k)
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have key : ∀ i j : ℕ, i < j → Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b i) =
      Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b j) →
      ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D,
        ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    intro i j hij hq
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hq.symm)
    have ht' : inc D ((b j : 𝓞 D.host.E) : D.host.E) - inc D ((b i : 𝓞 D.host.E) : D.host.E) =
        (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D ((t : 𝓞 D.host.E) : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) ht
      simp only [map_mul, map_sub, map_natCast] at this
      rw [← this, mul_comm]
    set U := (u : Formalism.MainNotions.StandardLatticesGL3.AE D)
    set V := ((u⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D)
    have hUV : U * V = 1 := Units.mul_inv u
    refine ⟨j - i, Nat.sub_pos_of_lt hij, (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) * V ^ i,
      mul_mem (sub_mem (add_mem (GlobalTheory.CongApprox.inc_mem_OhE D t) (hw j)) (hw i)) (pow_mem hu.2 i), ?_⟩
    have hj : U ^ j = U ^ (j - i) * U ^ i := by rw [← pow_add, Nat.sub_add_cancel hij.le]
    have e1 : U ^ j - U ^ i = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) := by
      rw [hb j, hb i]
      linear_combination ht'
    rw [Units.val_pow_eq_pow_val]
    calc U ^ (j - i) - 1 = (U ^ j - U ^ i) * V ^ i := by
          rw [hj, sub_mul, mul_assoc, ← mul_pow, hUV, one_pow, mul_one]
      _ = _ := by rw [e1, mul_assoc]
  obtain ⟨i, j, hij, hq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b k))
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hq
  · exact key j i h hq.symm

theorem absNorm_mem_conj (𝔪 : Ideal (𝓞 D.host.E)) : ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ 𝔪 (Ideal.absNorm_mem 𝔪)
  have h2 : D.host.conj • ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) = ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) := by
    first
    | exact smul_natCast _ _
    | simp
    | exact map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) _
  rw [h2] at this
  exact this

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem unitChar_pow_eq_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle,
    KillsCong ν 𝔪 → ∀ {n : ℕ} (β : GL (Fin n) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
    ∃ m : ℕ, 0 < m ∧ unitChar ν e β.val ^ m = 1 := by
  intro D e 𝔪 h𝔪 ν hν n β hβ hβ'
  have h0 := h𝔪.ne_bot
  obtain ⟨SS, c, he, -, -, -⟩ := h𝔪
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hd := det_mem_intAf hβ
  have hd' := det_mem_intAf hβ'
  have hdd : β.val.det * (β⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have huv : (1 - toEAf D e + toEAf D e * β.val.det) * (1 - toEAf D e + toEAf D e * (β⁻¹).val.det) = 1 := by
    linear_combination (1 - β.val.det - (β⁻¹).val.det + β.val.det * (β⁻¹).val.det) * hee + toEAf D e * hdd
  obtain ⟨x, a1, a2, a3⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit huv
  have hex : ∃ x, IsUnitDet e β.val x :=
    ⟨x, a1, a2, by rw [a3]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')⟩
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  set x0 := hex.choose
  have hx0 : toEAf D (x0 : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hN : 0 < Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0)) (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0))
  obtain ⟨m, hm, s, hs, hys⟩ := exists_pow_cong (Units.map (finHom D) x0) (intU_map x0 hx0 h3) hN
  have hinf : infPart D ((x0 ^ m : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, h1, one_pow]
  have hfin : IsFinIdl (x0 ^ m) ((Units.map (finHom D) x0) ^ m) := by
    rw [← map_pow]
    exact isFinIdl_map _ hinf
  have hU : IntU D ((Units.map (finHom D) x0) ^ m) := by
    have hu := intU_map x0 hx0 h3
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val]
      exact pow_mem hu.1 m
    · rw [← inv_pow, Units.val_pow_eq_pow_val]
      exact pow_mem hu.2 m
  have hmem : (((Units.map (finHom D) x0) ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈
      hatId D (𝔪 * D.host.conj • 𝔪) := by
    rw [hys]
    refine AddSubgroup.subset_closure ⟨((Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E), ?_, s, hs, ?_⟩
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_mul (Ideal.absNorm_mem 𝔪) (absNorm_mem_conj 𝔪)
    · simp only [map_natCast]
  have hk : ν (x0 ^ m) = 1 := hν _ _ hfin hU hmem
  have hc : ((ν x0)⁻¹ : Circle) ^ m = 1 := by rw [inv_pow, ← map_pow, hk, inv_one]
  refine ⟨m, hm, ?_⟩
  unfold unitChar
  rw [dif_pos hex]
  have := congrArg (fun z : Circle => (z : ℂ)) hc
  simpa using this

end GlobalTheory.StdRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEq
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.Move

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem eig_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    {g' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) (hH : H ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) : P.W.Om k 1 H = s • H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) = k := mul_one k
  have f2 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = s • P.W.Om 1 g' P.e0 := by
    rw [← e1, e2, he, P.W.smul _ _ _ _ hT]
  rw [hc', P.W.smul _ _ _ _ hH, smul_comm s c H] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_eig (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) :
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      s • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact eig_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)
    (GlobalTheory.FunObj.CosetFix.iop_facts hI P h𝔪).1 k s he

theorem exists_close {𝔪 : Ideal (𝓞 D.host.E)} (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)
    (z : Matrix (Fin d) (Fin a) D.host.E) (hz : Approx 𝔪 o k z) (m : ℕ) (hm : 0 < m) :
    ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧
      CloseTo D ⊤ m (k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
        (unitBlock D o a d) (z + w) := by
  choose b hb y hy hby using fun i j => GlobalTheory.CongApprox.exists_mem_approx D 𝔪 m hm _ (neg_mem (hz i j))
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have e1 : (((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := by
    simp
  unfold CloseTo
  refine fun i j => ⟨y i j, hy i j, Eq.trans ?_ (hby i j)⟩
  rw [e1, Matrix.one_mul, Matrix.map_add _ (map_add (inc D))]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply]
  ring

theorem wd_smul (δ : ℂ) {a d : ℕ} (x : VC D a d) (c : ℂ) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
  funext y
  simp only [Wd, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_cosetVec : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk c hc z hzi hz
  have h1 := hD.g1
  have he := P.vac.1
  have hIT := (GlobalTheory.FunObj.CosetFix.iop_facts hD P h𝔪).1
  have hfix := iop_eig hD P h𝔪 k c hc
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  obtain ⟨w, hw, hclose⟩ := exists_close o k z hz m hm
  have hmain := hl _ hclose
  rw [hfix, wd_smul] at hmain
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := (GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ ⊤ z
    (fun i j => (hzi i j).imp fun b hb => ⟨Submodule.mem_top, hb⟩)).1
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hIT
  unfold cosetVec cosV
  rw [P.W.smul _ _ _ _ hWT, hmain, ← h3, smul_comm]

end GlobalTheory.StdRead.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportional
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem lintegral_sq_split {Z X Y : Type} [TopologicalSpace Z] [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X]
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : Z ≃ₜ X × Y) (he : ∀ a b, e (a + b) = e a + e b)
    (μ : Measure Z) [μ.IsAddHaarMeasure] (μX : Measure X) [μX.IsAddHaarMeasure]
    {f g : Z → ℂ} (hf : Continuous f) (hg : Continuous g) (c : ℝ≥0∞)
    (h : ∀ y, ∫⁻ x, ‖f (e.symm (x, y))‖ₑ ^ 2 ∂μX = c * ∫⁻ x, ‖g (e.symm (x, y))‖ₑ ^ 2 ∂μX) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = c * ∫⁻ z, ‖g z‖ₑ ^ 2 ∂μ := by
  let E : Z ≃ₜ+ X × Y :=
    { e.toEquiv with
      map_add' := he
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let eM : Z ≃ᵐ X × Y := e.toMeasurableEquiv
  let μY : Measure Y := Measure.addHaar
  haveI hν : (μ.map E).IsAddHaarMeasure := inferInstance
  have hE : (E : Z → X × Y) = eM := rfl
  set s := Measure.addHaarScalarFactor (μ.map E) (μX.prod μY)
  have hs : μ.map E = s • (μX.prod μY) := Measure.isAddLeftInvariant_eq_smul _ _
  have key : ∀ F : Z → ℂ, Continuous F →
      ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
    intro F hF
    have hm : Measurable fun p : X × Y => ‖F (e.symm p)‖ₑ ^ 2 :=
      ((hF.comp e.symm.continuous).measurable.enorm.pow_const 2)
    calc ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = ∫⁻ p, ‖F (e.symm p)‖ₑ ^ 2 ∂(μ.map E) := by
          rw [hE, lintegral_map_equiv]; simp [eM]
      _ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
          rw [hs, lintegral_smul_measure, lintegral_prod_symm _ hm.aemeasurable]; rfl
  rw [key f hf, key g hg]
  have hmg : Measurable fun p : X × Y => ‖g (e.symm p)‖ₑ ^ 2 :=
    ((hg.comp e.symm.continuous).measurable.enorm.pow_const 2)
  simp_rw [h]
  rw [lintegral_const_mul _ (hmg.lintegral_prod_left' )]
  ring

end GlobalTheory.DoublingEvaluationL2

namespace GlobalTheory.DoublingEvaluationL2

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  intro F _ _ κ κ' _ _ A hA hL2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  let μX : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc⟩ := hL2 μX inferInstance
  constructor
  · intro μ hμ
    letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
    haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_left F κ κ κ' A hA) Φ hΦ
    refine lintegral_sq_split (Homeomorph.sumPiEquivProdPi κ κ' (fun _ => AF F)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
  · intro μ hμ
    letI mZ : MeasurableSpace (κ' ⊕ κ → AF F) := borel _
    haveI : BorelSpace (κ' ⊕ κ → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_right F κ' κ κ A hA) Φ hΦ
    refine lintegral_sq_split ((Homeomorph.sumPiEquivProdPi κ' κ (fun _ => AF F)).trans
        (Homeomorph.prodComm _ _)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceR hΦ y)

end GlobalTheory.DoublingEvaluationL2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZeroStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_normalisingVector_ne_zero : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0),
  Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ → oddE0 D cc δ t0 a d e0 →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d), W.Om x y e0 ≠ 0 := by
  first | exact @GlobalTheory.NormExact.om_normalising_ne_zero | exact GlobalTheory.NormExact.om_normalising_ne_zero | (intros; apply GlobalTheory.NormExact.om_normalising_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeScalarActionStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_lattice_scalar_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∃ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ, ∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (pure f M.vac) = c v γ • pure f M.vac := by
  first | exact @GlobalTheory.FinComm.vac_law | exact GlobalTheory.FinComm.vac_law | (intros; apply GlobalTheory.FinComm.vac_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominatorStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rational_support_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinSupp.exists_common_denominator | exact GlobalTheory.FinSupp.exists_common_denominator | (intros; apply GlobalTheory.FinSupp.exists_common_denominator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSeesawSchwartzStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_seesaw_schwartz : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  first | exact @GlobalTheory.SWTrans.exists_isTrans | exact GlobalTheory.SWTrans.exists_isTrans | (intros; apply GlobalTheory.SWTrans.exists_isTrans <;> assumption)
end

