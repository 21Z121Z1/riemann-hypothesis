import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

open Classical in

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] {K : Type} [Field K] (ψ : AddChar A K) (y : A) :
    IsIntegral ℤ (ψ y) := by
  refine IsIntegral.of_pow (Nat.card_pos (α := A)) ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact isIntegral_one

theorem qOf_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qOf w := by
  refine Nat.pos_of_ne_zero ?_
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem ciPsi_isIntegral {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : SB) (x : X.E) : IsIntegral ℤ (ciPsi Ch P x) := by
  classical
  unfold ciPsi
  split
  · have := ciFinite (X := X) (qOf_pos P.1).ne'
    exact addChar_isIntegral _ _
  · exact isIntegral_one

theorem twZeta_pow_eq_one {X : Fields} (σ₀ : X.K →+* ℂ) {N : ℕ} (hN : 0 < N)
    (hex : ∃ z : X.K, σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) : twZeta σ₀ N ^ N = 1 := by
  have hs : σ₀ (twZeta σ₀ N) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) := Classical.epsilon_spec hex
  apply σ₀.injective
  rw [map_pow, hs, map_one, ← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem twPsiQ_isIntegral {X : Fields} (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ)
    (hz : twZeta σ₀ (qOf P ^ D) ^ (qOf P ^ D) = 1) (a : X.E) : IsIntegral ℤ (twPsiQ σ₀ xi0 P D a) := by
  classical
  unfold twPsiQ
  split
  · refine IsIntegral.of_pow (pow_pos (qOf_pos P) D) ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow]
    exact isIntegral_one
  · exact isIntegral_one

theorem psi_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E),
    IsIntegral ℤ ((I.cst a).psi P x) := by
  intro B X I h ht a P x
  rw [ht.cst_eq a]
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [twCst_psi_g hP]
    exact ciPsi_isIntegral _ _ _
  · rw [twCst_psi_Q hP]
    exact twPsiQ_isIntegral _ _ _ _
      (twZeta_pow_eq_one _ (pow_pos (qOf_pos P.1) _) (TC.root_of_ok h ht.deep a P hP)) x

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSelfDualLatticeCoordsIffIntegralPosSpace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowLat

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

abbrev swi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F ⊗[F] E :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm.toAlgHom.toRingHom

theorem swi_sw (z : FiniteAdeleRing (𝓞 F) F ⊗[F] E) : swi F E (sw F E z) = z :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm_apply_apply z

theorem swi_tmul (a : FiniteAdeleRing (𝓞 F) F) (x : E) : swi F E (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := by
  show (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x
  rw [AlgEquiv.symm_apply_eq]; rfl

theorem mem_stdLat_iff {m : ℕ} (y : Fin m → E) :
    y ∈ Formalism.L2.Col.stdLat E m ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem intAf_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := fun v => ha v

theorem intAd_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => ha v

variable {n m : ℕ} (e : Fin n ≃ Fin m) (L : Set (Fin n → E))

theorem latHat_to_latS (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (w : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hw : w ∈ Formalism.MainNotions.StandardLattice.latHat F E L) :
    (fun j => sw F E (w (e.symm j))) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m) := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hmem : (1 : E) ⊗ₜ[F] a ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) :=
      Subring.subset_closure (Or.inr ⟨⟨a, intAf_mem ha⟩, rfl⟩)
    have hx' : (fun j => x (e.symm j)) ∈ Formalism.L2.Col.stdLat E m := (mem_stdLat_iff _).2 fun j => (hL x).1 hx _
    have h2 : (fun j => sw F E (a ⊗ₜ[F] x (e.symm j))) =
        (⟨_, hmem⟩ : Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) •
          (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) := by
      funext j
      show x (e.symm j) ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x (e.symm j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx', rfl⟩)
  | zero =>
    have : (fun j => sw F E ((0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (e.symm j))) = 0 := by
      funext j; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun j => sw F E ((y + z) (e.symm j))) = (fun j => sw F E (y (e.symm j))) + (fun j => sw F E (z (e.symm j))) := by
      funext j; simp
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : (fun j => sw F E ((-y) (e.symm j))) = -(fun j => sw F E (y (e.symm j))) := by
      funext j; simp
    rw [this]; exact neg_mem hy

theorem mul_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∀ w ∈ Formalism.MainNotions.StandardLattice.latHat F E L, (fun i => swi F E s * w i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hs using Subring.closure_induction with
  | mem s hs =>
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rcases hs with ⟨⟨c, hc⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
      · obtain ⟨o, rfl⟩ := RingHom.mem_range.1 hc
        apply AddSubgroup.subset_closure
        refine ⟨a, ha, fun i => algebraMap (𝓞 E) E o * x i, (hL _).2 fun i => ?_, ?_⟩
        · obtain ⟨p, hp⟩ := (hL x).1 hx i
          exact ⟨o * p, by rw [map_mul, hp]⟩
        · funext i
          show swi F E (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (a ⊗ₜ[F] x i) =
            a ⊗ₜ[F] (algebraMap (𝓞 E) E o * x i)
          rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      · apply AddSubgroup.subset_closure
        refine ⟨b * a, intAd_mem (mul_mem hb (intAf_mem ha)), x, hx, ?_⟩
        funext i
        show swi F E ((1 : E) ⊗ₜ[F] b) * (a ⊗ₜ[F] x i) = (b * a) ⊗ₜ[F] x i
        rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero =>
      have : (fun i => swi F E s * (0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) i) = 0 := by
        funext i; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun i => swi F E s * (y + z) i) = (fun i => swi F E s * y i) + (fun i => swi F E s * z i) := by
        funext i; simp [mul_add]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun i => swi F E s * (-y) i) = -(fun i => swi F E s * y i) := by
        funext i; simp
      rw [this]; exact neg_mem hy
  | zero =>
    intro w _
    have : (fun i => swi F E 0 * w i) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | one =>
    intro w hw
    have : (fun i => swi F E 1 * w i) = w := by funext i; simp
    rw [this]; exact hw
  | add s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s + t) * w i) = (fun i => swi F E s * w i) + (fun i => swi F E t * w i) := by
      funext i; simp [add_mul]
    rw [this]; exact add_mem (hs w hw) (ht w hw)
  | neg s _ hs =>
    intro w hw
    have : (fun i => swi F E (-s) * w i) = -(fun i => swi F E s * w i) := by
      funext i; simp
    rw [this]; exact neg_mem (hs w hw)
  | mul s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s * t) * w i) = (fun i => swi F E s * (fun i => swi F E t * w i) i) := by
      funext i; simp [mul_assoc]
    rw [this]; exact hs _ (ht w hw)

theorem latS_to_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hv : v ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)) :
    (fun i => swi F E (v (e i))) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨1, intAd_mem (one_mem _), fun i => x (e i), (hL _).2 fun i => (mem_stdLat_iff x).1 hx _, ?_⟩
    funext i
    show swi F E (x (e i) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x (e i)
    exact swi_tmul _ _
  | zero =>
    have : (fun i => swi F E ((0 : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (e i))) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => swi F E ((y + z) (e i))) = (fun i => swi F E (y (e i))) + (fun i => swi F E (z (e i))) := by
      funext i; simp
    rw [this]; exact add_mem hy hz
  | smul s y _ hy =>
    have : (fun i => swi F E ((s • y) (e i))) = (fun i => swi F E (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (fun i => swi F E (y (e i))) i) := by
      funext i
      show swi F E ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * y (e i)) = _
      rw [map_mul]
    rw [this]; exact mul_latHat L hL _ s.2 _ hy

theorem mem_iff_swap (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E))
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (x : Fin n → E) :
    ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L ↔
      (fun j => x (e.symm j)) ∈ Formalism.UG.CS.globLat
        (Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g)) (Formalism.L2.Col.stdLat E m) := by
  set w := ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) with hw
  have hv : (((Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g))⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).mulVec
        (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) = fun j => sw F E (w (e.symm j)) := by
    rw [← map_inv, ← map_inv]
    funext j
    rw [hw]
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Formalism.UG.inclE]
  show w ∈ _ ↔ _ ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)
  rw [hv]
  constructor
  · exact latHat_to_latS e L hL w
  · intro h
    have := latS_to_latHat e L hL _ h
    simpa [swi_sw] using this

end Gen

theorem mem_selfDualLatticeCoords_iff_integral_posSpace (D : D7) (W : HSpace D.host.E) (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (hW : W = Formalism.BasicNotions.Examples₂.posSpace hstar N) (x : Fin W.rank → D.host.E) :
    x ∈ L0c D W ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  subst hW
  revert x
  show ∀ x : Fin N → D.host.E, (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) ∈ Formalism.BasicNotions.Examples₂.stdLat N ↔
    ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)
  intro x
  have hsum : (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) = x := by
    simpa only [Pi.basisFun_repr] using (Pi.basisFun D.host.E (Fin N)).sum_repr x
  rw [hsum, Formalism.BasicNotions.Examples₂.stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    have e1 : (∑ j, c j • (Pi.basisFun D.host.E (Fin N)) j) i = c i • (1 : D.host.E) := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.basisFun_apply]
      · intro b _ hb
        simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
      · simp
    rw [← congrFun hc i, e1, Algebra.smul_def, mul_one]
  · intro hx
    choose c hc using hx
    refine ⟨c, ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply, Algebra.smul_def, hc]
    · intro b _ hb
      simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
    · simp

theorem mem_selfDualLatticeCoords_iff_integral_rowSpace (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok)
    (x : Fin X.toD7.sp.X'.rank → X.toD7.host.E) :
    x ∈ L0c X.toD7 X.toD7.sp.X' ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 X.toD7.host.E) X.toD7.host.E) := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  exact mem_selfDualLatticeCoords_iff_integral_posSpace X.toD7 X.toD7.sp.X' hs _ h2 x

theorem hLat_eq_decoAd_N : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), X.B.fields.Ok → I.Ok →
    ∀ (U : Set I.ι) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X'),
      Bridge.hLat X.toD7.sp.X' h = ((RowAd.decoAd X I t h).1.N).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap := by
  intro X px I _ hI U t h
  have hN : (RowAd.decoAd X I t h).1.N = Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _) := by
    unfold RowAd.decoAd Formalism.L2.Col.decoOf
    split_ifs with h1
    · rfl
    · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (RowDeco.ptE_mem_UAd X I hI h)) h1
  rw [hN]
  unfold Bridge.hLat
  conv_rhs => rw [← Submodule.span_eq ((Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _)).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap)]
  congr 1
  ext x
  exact (mem_iff_swap (finCongr (RowAd.rank_X' X)) (L0c X.toD7 X.toD7.sp.X') (mem_selfDualLatticeCoords_iff_integral_rowSpace X I hI) h.1 x).trans
    (Submodule.mem_map_equiv (e := LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm) _).symm

end GlobalTheory.Mem.R3.RowLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    GlobalTheory.T.existsLayeredData_of_goodScaleContexts hAll Q' QO
      (GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NchTOfTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.NchAt

set_option maxHeartbeats 4000000 in

theorem tie_of_true {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'} {tp' : TupTied D' cf' C'}
    (b : NTrue hL D' cf' C' tp') : NChTie D' C' ∧ PsiChoiceCompatible D' cf' C' tp' := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := b
  subst eq
  cases pack
  refine ⟨⟨Sp.twOf_eq, Sp.twSide_eq, fun a => ?_, ?_, ch.nct.embedding_baseField_condition⟩, ch.psi⟩
  · exact (Sp.Q_eq _ _ a (((L.X.nd.locs_mem _ _ a).2 ⟨rfl, rfl⟩))).trans (Sp.Qc_eq _ _)
  · obtain ⟨ψ0, hc, hw, -⟩ := ch.nct.psi_eq
    exact ⟨ψ0, hc, hw, fun a g => Sp.psi_eq a g _ (hw _ g)⟩

end GlobalTheory.HeightCounting.NchAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

open scoped TensorProduct

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

def NearV (P : SBof I a)
    (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) : Prop :=
  GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (GlobalTheory.Mem.Col2.ChartLevel.emb v x) (GlobalTheory.TwU.seamGL (sm I l Z) g)

def NearPair (P : SBof I a)
    (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z ∧ NearV I l Z a v P x g

def NearSet : Set (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
  {x | ∀ P : SBof I a, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ g z, NearPair I l Z a v P x g z}

open Classical in

def valV (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) : ℂ :=
  (sm I l Z).σ₀ (∏ P : SBof I a,
    if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1)

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

end GlobalTheory.Mem.Df
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

noncomputable def iw0 {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) :
    D.host.E →+* (D.gat u v hg).P.Qq q :=
  ((G u v hg).eQ q _ rfl).symm.toRingHom.comp
    (((RingHom.fst _ _).comp ((G u v hg).spl _ ((G u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F)))

theorem splitPlaceIdempotent_cmEmbedding_compat {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) (x : D.host.E) :
    (G u v hg).eQ q _ rfl (iw0 G u v hg q x) =
      ((G u v hg).spl _ ((G u v hg).pl q).2
        (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F) x)).1 := by
  simp [iw0]

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameMatrixMemUnipotentIffColumnSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond | exact GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond | (intros; apply GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond <;> assumption)
end

