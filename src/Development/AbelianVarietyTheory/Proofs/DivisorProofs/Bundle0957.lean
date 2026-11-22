import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0888
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn IsDatum TwistedTransport)

namespace GlobalTheory.TwistedTransportProof

variable {E : Type} [Field E] [NumberField E]

theorem modF_rat (y : (Af E)ˣ) : ∃ q : ℚ, (q : ℝ) = modF y := by
  unfold modF
  refine finprod_induction (fun x : ℝ => ∃ q : ℚ, (q : ℝ) = x) ⟨1, by simp⟩ ?_ ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; ring⟩
  · intro v
    exact ⟨((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), by push_cast; rfl⟩

theorem isAlgebraic_modF_pow (y : (Af E)ˣ) (s : ℕ) : IsAlgebraic ℚ (((modF y ^ s : ℝ)) : ℂ) := by
  obtain ⟨q, hq⟩ := modF_rat y
  rw [← hq]
  have : ((((q : ℝ) ^ s : ℝ)) : ℂ) = algebraMap ℚ ℂ (q ^ s) := by simp
  rw [this]; exact isAlgebraic_algebraMap _

theorem lattice_princ_mul (c : Ideal (OF E)) (y : (Af E)ˣ) (a : Eˣ) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom a * y) = (fun x => (a : E) * x) '' lattice c y := by
  ext z
  constructor
  · intro hz
    refine ⟨(a : E)⁻¹ * z, ?_, by simp⟩
    rw [← mul_mem_lattice_princ c y a]
    simpa using hz
  · rintro ⟨x, hx, rfl⟩
    exact (mul_mem_lattice_princ c y a x).2 hx

theorem exists_isLatSum_of_mk_eq [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ)
    (κ : I → ℕ) {c : Ideal (OF E)} {y y' : (Af E)ˣ} (h : (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y')
    {S : ℂ → ℂ} (hS : IsLatSum φ (2 * s) κ (lattice c y) S) : ∃ S', IsLatSum φ (2 * s) κ (lattice c y') S' := by
  classical
  rw [QuotientGroup.eq] at h
  obtain ⟨p, ⟨a, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 h
  have e1 : y * (Units.map (algebraMap E (Af E)).toMonoidHom a * u) = y' := by rw [hpu, mul_inv_cancel_left]
  have e : y' = Units.map (algebraMap E (Af E)).toMonoidHom a * y * u := by rw [← e1]; ac_rfl
  rw [e, lattice_mul_unit _ hu, lattice_princ_mul]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s (lattice c y) κ a S hS).1⟩

theorem coordIn_eq {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold coordIn; ring

abbrev lv (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

theorem lv_mul (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z) = lv χ s y * lv χ s z := by
  simp only [lv, map_mul, Units.val_mul, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, mul_pow]
  push_cast; ring

theorem lv_ne_zero (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : lv χ s y ≠ 0 :=
  GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ y

theorem lv_mul_inv (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z⁻¹) = lv χ s y * (lv χ s z)⁻¹ := by
  have h := lv_mul χ s (y * z⁻¹) z
  rw [inv_mul_cancel_right] at h
  rw [h, mul_inv_cancel_right₀ (lv_ne_zero χ s z)]

theorem isAlgebraic_lv [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hU : UnramFin E) (h𝔣 : IsBaseCond 𝔣)
    (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (hV : IsValChar φ s κ 𝔣 ∅ χ) [Finite (PicO (condQ 𝔣 Q))] (y : (Af E)ˣ) :
    IsAlgebraic ℚ (lv χ s y) := by
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hu : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ u = 1 := fun u hu => hu0 u (hatOUnits_mono hle hu)
  have h1 := GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hV.2.2.1 hu y
  exact h1.mul (isAlgebraic_modF_pow y s)

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem isAlgebraic_unit_val {G : Type} [Group G] [Finite G] (ψ : G →* ℂˣ) (q : G) : IsAlgebraic ℚ ((ψ q : ℂˣ) : ℂ) := by
  have h : ((ψ q : ℂˣ) : ℂ) ^ (Nat.card G) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact IsAlgebraic.of_pow Nat.card_pos (by rw [h]; exact isAlgebraic_one)

theorem alg_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {Λ₀ : PeriodPair} {Ω₀ : ℂ} (hΛ₀ : IsLatOf ι 1 Λ₀) (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀)
    (hA : LatAlg) (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (hD : IsDatum ι φ s κ 𝔣 Q χ) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T) :
    IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((ψ q : ℂˣ) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out)⁻¹ * S q 0) =
      ((ψ q : ℂˣ) : ℂ)⁻¹ * (lv χ s q.out)⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, lv]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ₀ hΩ₀ E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h2 := isAlgebraic_lv hφ hU h𝔣 hQ hV q.out
  have h3 := isAlgebraic_unit_val ψ q
  refine mul_mem (mul_mem (inv_mem ?_) (inv_mem ?_)) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof
theorem key_alg (a b l1 l2 lu C N S : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hu : lu ≠ 0) :
    a⁻¹ * l1⁻¹ * (C * (N⁻¹ * S)) = C * (N⁻¹ * (lu * b)⁻¹ * ((a * b⁻¹)⁻¹ * l2⁻¹ * (l2 * ((l1 * lu⁻¹)⁻¹ * S)))) := by
  field_simp
end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem conj_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {g : ℂ ≃+* ℂ} {t : (Af K)ˣ} {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ}
    (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀) (hTT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hC : LatConj)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (hD : IsDatum ι φ s κ 𝔣 Q χ)
    (κ' : I → ℕ) (χ' : HChar E) (hw : IsConjWt φ g κ κ') (hcc : IsConjChar φ s κ' g χ χ')
    (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T)
    (hT' : IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T') :
    g (coordIn E d s κ Ω₀ T) =
      coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
        (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T') := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  obtain ⟨-, S', hS', rfl⟩ := hT'
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  obtain ⟨ct, hct⟩ : ∃ ct, classOf K (condQ 𝔣 Q) t = ct := ⟨_, rfl⟩
  rw [hct]
  have hct' : ct = QuotientGroup.mk (upIdele K E t) := by rw [← hct, GlobalTheory.ToricRatioBridge.upIdele_eq]; rfl
  set N : ℂ := ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) with hN
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hχu : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ w = 1 := fun w hw => hu0 w (hatOUnits_mono hle hw)
  have hχ'u : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ' w = 1 := fun w hw => by
    have h1 := hcc.1 w
    have hm := GlobalTheory.CMVal.LUnit.modF_of_mem_hatOUnits hw
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF, hχu w hw, hm] at h1
    simpa using h1
  have hmk : ∀ q : PicO (condQ 𝔣 Q), (QuotientGroup.mk (q * ct⁻¹).out : PicO (condQ 𝔣 Q)) = QuotientGroup.mk (q.out * (upIdele K E t)⁻¹) := fun q => by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hct']
  choose S'' hS'' using fun q : PicO (condQ 𝔣 Q) => exists_isLatSum_of_mk_eq hφ s κ' (hmk q) (hS' (q * ct⁻¹))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, coordIn_eq d s κ Ω₀, coordIn_eq d s κ Ω₁]
  simp only [Finset.mul_sum, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight ct⁻¹) _ _ fun q => ?_
  simp only [Equiv.coe_mulRight]
  have hg1 : g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out) = lv χ' s q.out := (hcc.1 q.out).symm
  have hg2 := hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ κ' hw q.out (S q) (S'' q)
    (hS q) (hS'' q)
  have h' : (lv χ' s (q.out * (upIdele K E t)⁻¹))⁻¹ * S'' q 0 = (lv χ' s (q * ct⁻¹).out)⁻¹ * S' (q * ct⁻¹) 0 :=
    GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hcc.2 hχ'u (q.out * (upIdele K E t)⁻¹) (q * ct⁻¹).out (S'' q)
      (S' (q * ct⁻¹)) (hmk q).symm (hS'' q) (hS' (q * ct⁻¹))
  rw [lv_mul_inv, eq_inv_mul_iff_mul_eq₀ (lv_ne_zero _ _ _)] at h'
  have hsplit : ∀ a b : ℂ, coordIn E d s κ Ω₀ 1 * (a * b * S q 0) = a * b * coordIn E d s κ Ω₀ (S q 0) := fun a b => by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; ring
  have e1 : ((conjChar g ψ (q * ct⁻¹) : ℂˣ) : ℂ) = g (ψ q) * (g (ψ ct))⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [hsplit, map_mul, map_mul, map_inv₀, map_inv₀, hg1, hg2, coordIn_eq d s κ Ω₁ (N⁻¹ * S'' q 0), ← h', e1,
    GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar]
  have n1 := lv_ne_zero χ' s q.out
  have n2 := lv_ne_zero χ' s (q * ct⁻¹).out
  have n3 := lv_ne_zero χ' s (upIdele K E t)
  have n4 : g (ψ q) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  have n5 : g (ψ ct) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  exact key_alg _ _ _ _ _ _ _ _ n4 n5 n1 n2 n3

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem twistedTransport_of_latClaims (hP : PeriodEx) (hA : LatAlg) (hC : LatConj) : TwistedTransport := by
  intro K _ _ d δ ι h2 hd hδ
  haveI : IsTotallyComplex K := GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg hd hδ
  obtain ⟨Λ₀, hΛ₀⟩ := GlobalTheory.LatVal.Model.exists_isLatOf d δ ι h2 hd hδ
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ₀) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ₀]; norm_num)
  refine ⟨Ω₀, hΩ₀0, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD ψ T hT =>
    alg_part h2 hd hδ hΛ₀ hΩ₀ hA E I φ s κ 𝔣 Q χ hD ψ T hT, ?_⟩
  intro Ω _ _ _ j art hj hart g σ t hσ hsym
  obtain ⟨Λ₁, Ω₁, hTT⟩ := hP K ι h2 Λ₀ Ω₀ hΛ₀ hΩ₀0 Ω j art hj hart g σ t hσ hsym
  exact ⟨Ω₁, hTT.2.1, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT' =>
    conj_part h2 hd hδ hΩ₀ hTT hC E I φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT'⟩

end GlobalTheory.TwistedTransportProof

open GlobalTheory.TwistedTransportProof in

theorem GlobalTheory.TwistedTransportProof.main : PeriodEx → LatAlg → LatConj → GlobalTheory.ToricTransport.TwistedTransport :=
  twistedTransport_of_latClaims
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatReflection

theorem latHat_eq_lamHat {D : D7} (V : HSp D) : Formalism.L2.Pj.latHat V = Formalism.L2.NTheta.LamHat V := by
  rw [GlobalTheory.LatDual.lamHat_eq_hat]
  exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1

end GlobalTheory.LatReflection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorIndicatorMemHecke
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.DivIndU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def diagGL {n : ℕ} (x : Fin n → L) (hx : ∀ i, x i ≠ 0) : GL (Fin n) L :=
  ⟨Matrix.diagonal x, Matrix.diagonal fun i => (x i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hx i),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hx i)⟩

end GlobalTheory.DivIndU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_integral_adelic_element_exists : ∀ (D : D7) (n : ℕ) (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (EAf D)) (G : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), (intGL D.host.F D.host.E n G).val = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val * J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val → ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ x ∈ UA D.sp.cm J, x ∈ St β → ∀ (w' : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)), w'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal → (v ∉ S → redFn (β * intGL D.host.F D.host.E n y) w' x = redFn β w' x) ∧ (v ∈ S → ∀ w : Pl D.host.E, IsConjPl w w' → ∀ (p : ℕ) (e : kP w ≃+* ZMod p) (e' : ZMod p ≃+* kP w') (i j : Fin n), (redFn (β * intGL D.host.F D.host.E n y) w' x).val i j = e' (e (((redFn β w x)⁻¹).val j.rev i.rev))) := by
  first | exact @GlobalTheory.FrameMove.exists_frame_move | exact GlobalTheory.FrameMove.exists_frame_move | (intros; apply GlobalTheory.FrameMove.exists_frame_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  intro p _ K hK r hr x
  have hit : ∀ (i : ℕ) (y : Kn p K r),
      (((⇑(frobR p K r))^[i] y : Kn p K r) : PadicAlgCl p) = (frobK p K ^ i) (y : PadicAlgCl p) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  apply Subtype.ext
  rw [hit]
  exact (IsFrobOn.pow_fixes_iff p K hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ x.2

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRComp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ValuationCompositionDivisor

theorem valR_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y)
    (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  unfold valR
  rfl

end GlobalTheory.ValuationCompositionDivisor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw

variable {Rg : Type} [CommRing Rg]

def ringOf {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom

def cstT {T : Scheme.{0}} (t : T ⟶ Sp Rg) : Rg →+* Γ(T, ⊤) :=
  t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom

theorem ringOf_X {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (k : Fin n) :
    ringOf g (MvPolynomial.X k) = coord g k := rfl

def expand (mA mB : ℕ) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C)
    (fun j => ∑ i, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i) F

variable {A₀ : Scheme.{0}} {N : LB A₀} {mA : ℕ}

def monSec (a : Fin mA → LB.Sec N) (d : ℕ) (ν : Fin mA →₀ ℕ) : LB.Sec (GlobalTheory.AbLaw.pw N (d : ℤ)) where
  f := fun q => if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0
  compat := fun (q q' : N.ι) => by
    change (A₀.presheaf.map (homOfLE (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q)).op).hom
        (if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0) =
      ((N.g q q' ^ (d : ℤ) : Γ(A₀, N.U q ⊓ N.U q')ˣ) : Γ(A₀, N.U q ⊓ N.U q')) *
        (A₀.presheaf.map (homOfLE (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q')).op).hom
          (if ∑ i, ν i = d then ∏ i, ((a i).f q') ^ ν i else 0)
    split_ifs with h
    · simp only [map_prod, map_pow]
      simp only [(a _).compat, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    · simp only [map_zero, mul_zero]

omit [CommRing Rg] in
theorem idPb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) :
    IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

variable {X : Scheme.{0}} {M : LB X}

def vecOf {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : Fin Q.a → Rg :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).1

theorem vecOf_ker {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : (Q.D₀.map (RingHom.id Rg)).mulVec (vecOf Q s) = 0 :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).2

theorem vecOf_spec {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) (i : Q.I) :
    rs X (le_pull M (𝟙 X) (Q.le i)) ((finSecPullId s).f (fun _ => Q.ch i)) =
      ∑ k, cst f ((𝟙 X) ⁻¹ᵁ Q.W i) (vecOf Q s k) * (Scheme.Hom.app (𝟙 X) (Q.W i)).hom (Q.u k i) := by
  have h := (Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose_spec
    ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)) i
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {mB : ℕ} {f : A₀ ⟶ Sp Rg}

def polys (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (d : ℕ) (F : MvPolynomial (Fin mB) Rg)
    (k : Fin (Q d).a) : MvPolynomial (Fin (mA * mB)) Rg :=
  ∑ ν ∈ (expand mA mB F).support, (expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k)

def formIdeal (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) {B₀ : Scheme.{0}} {H : LB B₀}
    (fB : B₀ ⟶ Sp Rg) (b : Fin mB → LB.Sec H) : Ideal (MvPolynomial (Fin (mA * mB)) Rg) :=
  Ideal.span {P | ∃ (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (k : Fin (Q d).a),
    F.IsHomogeneous d ∧ Kills fB b F ∧ P = polys Q a d F k}

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalPairPowerSumVanish
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CentreCpt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem val_eq_one_of_pow_eq_one (hN : N ≠ 0) {x : ValueGroupWithZero k} (h : x ^ N = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

theorem mem_KO_of_mem_center {w : GL (Fin N) k} (hw : w ∈ Subgroup.center (GL (Fin N) k))
    (hv : valuation k (w : Matrix (Fin N) (Fin N) k).det = 1) : w ∈ KO k (Fin N) := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hw
  obtain ⟨a, rfl⟩ := hw
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hdet : ((GeneralLinearGroup.scalar (Fin N) a : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
      (a : k) ^ N := by
    simp [Matrix.det_diagonal]
  rw [hdet, map_pow] at hv
  have ha : valuation k (a : k) = 1 := val_eq_one_of_pow_eq_one hN.ne' hv
  have hai : valuation k ((a⁻¹ : kˣ) : k) = 1 := by simp [ha]
  have ent : ∀ b : kˣ, valuation k (b : k) = 1 → ∀ i j : Fin N,
      ((GeneralLinearGroup.scalar (Fin N) b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := by
    intro b hb i j
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 hb.le
    · exact zero_mem _
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨ent a ha, ent a⁻¹ hai⟩

def vdet (k : Type) [Field k] [ValuativeRel k] (N : ℕ) : GL (Fin N) k →* ValueGroupWithZero k :=
  (valuation k).toMonoidWithZeroHom.toMonoidHom.comp ((Units.coeHom k).comp GeneralLinearGroup.det)

theorem vdet_apply (g : GL (Fin N) k) : vdet k N g = valuation k (g : Matrix (Fin N) (Fin N) k).det := rfl

theorem vdet_eq_one_of_mem_KO {g : GL (Fin N) k} (hg : g ∈ KO k (Fin N)) : vdet k N g = 1 := by
  have hle : ∀ h ∈ KO k (Fin N), vdet k N h ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    rw [vdet_apply]
    change valuation k ((algebraMap 𝒪[k] k).mapMatrix (u : Matrix (Fin N) (Fin N) 𝒪[k])).det ≤ 1
    rw [← RingHom.map_det]
    exact ((Valuation.mem_integer_iff _ _).1 (u.val.det).2)
  have h1 := hle g hg
  have h2 := hle g⁻¹ (inv_mem hg)
  have h3 : vdet k N g * vdet k N g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = vdet k N g * vdet k N g⁻¹ := h3.symm
    _ ≤ vdet k N g * 1 := by gcongr
    _ = vdet k N g := mul_one _

theorem exists_compact_center_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C →
    ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C,
      ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  intro k _ _ _ _ N C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : GL (Fin N) k => c • (KO k (Fin N) : Set (GL (Fin N) k)))
    (fun c => GlobalTheory.SplitFlip.isOpen_KO.smul c)
    (fun c _ => Set.mem_iUnion.2 ⟨c, 1, one_mem _, mul_one c⟩)
  let f : GL (Fin N) k → GL (Fin N) k := fun i =>
    if h : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 then h.choose * i else 1
  refine ⟨⋃ i ∈ t, f i • (KO k (Fin N) : Set (GL (Fin N) k)),
    t.isCompact_biUnion fun i _ => GlobalTheory.SplitFlip.isCompact_KO.smul (f i), ?_⟩
  intro z hz c hc hzc
  rw [← vdet_apply] at hzc
  obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (ht hc)
  obtain ⟨κ, hκ, rfl⟩ := hci
  change z * (i * κ) ∈ _
  change vdet k N (z * (i * κ)) = 1 at hzc
  have hvκ := vdet_eq_one_of_mem_KO hκ
  have hzi : vdet k N (z * i) = 1 :=
    calc vdet k N (z * i) = vdet k N (z * i) * vdet k N κ := by rw [hvκ, mul_one]
      _ = 1 := by rw [← map_mul, mul_assoc, hzc]
  have hex : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 := ⟨z, hz, hzi⟩
  have hfi : f i = hex.choose * i := dif_pos hex
  obtain ⟨hzc', hv'⟩ := hex.choose_spec
  set zi := hex.choose
  set w := z * zi⁻¹ with hw
  have hwc : w ∈ Subgroup.center (GL (Fin N) k) := mul_mem hz (inv_mem hzc')
  have hwv : vdet k N w = 1 :=
    calc vdet k N w = vdet k N w * vdet k N (zi * i) := by rw [hv', mul_one]
      _ = vdet k N (z * i) := by rw [← map_mul, ← mul_assoc, hw, inv_mul_cancel_right]
      _ = 1 := hzi
  have hwK : w ∈ KO k (Fin N) := mem_KO_of_mem_center hwc (by rw [← vdet_apply]; exact hwv)
  refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
  rw [hfi]
  refine ⟨w * κ, mul_mem hwK hκ, ?_⟩
  have hz' : z = w * zi := by rw [hw, inv_mul_cancel_right]
  have hcomm := Subgroup.mem_center_iff.1 hwc
  change zi * i * (w * κ) = z * (i * κ)
  rw [hz', ← mul_assoc, hcomm (zi * i)]
  simp only [mul_assoc]

end GlobalTheory.CentreCpt
end
end

