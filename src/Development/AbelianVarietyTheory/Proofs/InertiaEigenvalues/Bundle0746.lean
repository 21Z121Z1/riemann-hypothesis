import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.SatakeDualWeyl.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhere
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLevel

section MixMat
variable {R : Type*} [CommRing R] {n : ℕ}

theorem mix_mul (p : R) (hp : p * p = p) (A B C D : Matrix (Fin n) (Fin n) R) :
    (p • A + (1 - p) • B) * (p • C + (1 - p) • D) = p • (A * C) + (1 - p) • (B * D) := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [mul_comm, h1]
  have h3 : (1 - p) * (1 - p) = 1 - p := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hp, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_one (p : R) : p • (1 : Matrix (Fin n) (Fin n) R) + (1 - p) • 1 = 1 := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem conjT_mix (σ : R →+* R) (p : R) (hp : σ p = p) (A B : Matrix (Fin n) (Fin n) R) :
    conjT σ (p • A + (1 - p) • B) = p • conjT σ A + (1 - p) • conjT σ B := by
  ext i j
  simp [conjT, map_sub, hp]

end MixMat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_GA_iff (x : GL (Fin n) (AL L)) :
    x ∈ ReciprocityTheory.Aut.GA L n ↔ (x : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x = 1 := Iff.rfl

def mixG (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) : GAf L n :=
  ⟨⟨p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)),
    p • ((g.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) +
      (1 - p) • ((h.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)),
    by rw [mix_mul p hp, Units.mul_inv, Units.mul_inv, mix_one],
    by rw [mix_mul p hp, Units.inv_mul, Units.inv_mul, mix_one]⟩, by
    rw [mem_GA_iff]
    show (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) *
      conjT (conjAL L) (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) = 1
    rw [conjT_mix _ p hc, mix_mul p hp, (mem_GA_iff _).1 g.2, (mem_GA_iff _).1 h.2, mix_one]⟩

theorem mixG_val (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) :
    ((mixG p hp hc g h).1 : Matrix (Fin n) (Fin n) (AL L)) =
      p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax in

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

section Idem
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))

theorem compAt_idemAt_self : compAt L v (idemAt v) = 1 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, ← Algebra.TensorProduct.one_def]

theorem compAt_idemAt_ne {w} (hw : w ≠ v) : compAt L w (idemAt v) = 0 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self : idemAt (L := L) v * idemAt v = idemAt v := by
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · rw [compAt_idemAt_ne v hw]; simp

theorem conjAL_idemAt : conjAL L (idemAt v) = idemAt v := by
  simp [idemAt, conjAL, Algebra.TensorProduct.map_tmul]

theorem idemAt_mem : idemAt (L := L) v ∈ ALint L :=
  GlobalTheory.InertUmax.one_tmul_sgl_mem L v 1 (one_mem _)

theorem one_sub_idemAt_mem : 1 - idemAt (L := L) v ∈ ALint L :=
  Subring.sub_mem _ (one_mem _) (idemAt_mem v)

theorem one_entry_mem (S : Subring (AL L)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ S := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_entry (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem away_eq_zero {x : GAf L n} (hx : TrivOutside {v} x) (i j : Fin n) :
    (1 - idemAt v) * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_mul, map_sub, map_sub, map_one, compAt_one_entry]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
    rw [Matrix.map_apply] at h
    rw [h, sub_self, mul_zero]

end Idem

def DivBy (N : ℕ) (M : Matrix (Fin n) (Fin n) (AL L)) : Prop :=
  ∀ i j, ∃ y ∈ ALint L, M i j = (N : AL L) * y

theorem DivBy.add {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) (hB : DivBy N B) :
    DivBy N (A + B) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  obtain ⟨z, hz, f⟩ := hB i j
  exact ⟨y + z, Subring.add_mem _ hy hz, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem DivBy.neg {N : ℕ} {A : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) : DivBy N (-A) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  exact ⟨-y, Subring.neg_mem _ hy, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem DivBy.mul_int {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (A * B) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, y i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hB k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum, mul_assoc]⟩

theorem DivBy.int_mul {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (B * A) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, B i k * y k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hB i k) (hy k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring⟩

def levelAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧
    DivBy N ((1 - idemAt v) • ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) - 1))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Umax L n).mul_mem ha hb, ?_⟩
    have e : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) * (b.1 : Matrix (Fin n) (Fin n) (AL L)) +
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul]
    exact (ha'.mul_int hb).add hb'
  one_mem' := ⟨(Umax L n).one_mem, fun i j => ⟨0, zero_mem _, by simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Umax L n).inv_mem ha, ?_⟩
    have e : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        -(((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
      rw [mul_sub, mul_one]
      have : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]; abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    exact (ha'.int_mul ((Umax L n).inv_mem ha)).neg

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem exists_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  intro L _ _ _ n v N _
  have hp := idemAt_mul_self (L := L) v
  have hc := conjAL_idemAt (L := L) v
  refine ⟨levelAt (n := n) v N, ?_, ?_, ?_⟩
  · rintro κ ⟨hU, hκ⟩
    refine ⟨hU, fun i j => ?_⟩
    obtain ⟨y, hy, e⟩ := hκ i j
    refine ⟨(1 - idemAt v) * y, Subring.mul_mem _ (one_sub_idemAt_mem v) hy, ?_⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, e]; ring
  · intro κ hκ
    refine ⟨fun h => h.1, fun h => ⟨h, fun i j => ⟨0, zero_mem _, ?_⟩⟩⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, away_eq_zero v hκ, mul_zero]
  · rintro κ ⟨hU, hκ⟩
    refine ⟨mixG (idemAt v) hp hc κ 1, mixG (idemAt v) hp hc 1 κ, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, mix_mul _ hp, OneMemClass.coe_one, Units.val_one,
        mul_one, one_mul]
      rw [← add_smul, add_sub_cancel, one_smul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (hU i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
    · intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne v hw']
      simp only [OneMemClass.coe_one, Units.val_one, compAt_one_entry, zero_mul, zero_add, sub_zero, one_mul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (hU i j))
    · intro i j
      obtain ⟨y, hy, e⟩ := hκ i j
      refine ⟨y, hy, ?_⟩
      rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e
      rw [← e, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      simp only [OneMemClass.coe_one, Units.val_one]
      ring
    · intro x hx
      have hX : (x.1 : Matrix (Fin n) (Fin n) (AL L)) =
          idemAt v • (x.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - idemAt v) • 1 := by
        ext i j
        have h := away_eq_zero v hx i j
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
        linear_combination h
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, OneMemClass.coe_one, Units.val_one]
      rw [hX, mix_mul _ hp, mix_mul _ hp]
      simp only [mul_one, one_mul]

end GlobalTheory.InertLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruence
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongOpen

section Lemmas

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem kappa_one_tmul (F : FinIso L n) (a : AFplus L) :
    F.κ (1 ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  refine FiniteAdeleRing.ext _ fun w ↦ ?_
  obtain ⟨i, hi, hia⟩ := F.right w (w.under (𝓞 (maximalRealSubfield L))) rfl
  rw [hia, GlobalTheory.DefU.ClassFin.adMap_eq_complMap rfl]
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
    (w.under (𝓞 (maximalRealSubfield L)))).equalizer hi
    (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k ↦ ?_)) _
  change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap]
  have h1 : (algebraMap (maximalRealSubfield L) (AFplus L) k) (w.under (𝓞 (maximalRealSubfield L))) =
      algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (w.under (𝓞 (maximalRealSubfield L)))) k := rfl
  rw [← h1, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
  rfl

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ (x ⊗ₜ a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  rw [← kappa_one_tmul, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem mem_ALint_of_kappa (F : FinIso L n) {y : AL L} (hy : F.κ y ∈ Formalism.UG.intAd L) :
    y ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (F := maximalRealSubfield L) (E := L)
    (ι := F.κ.toRingHom) (fun x a ↦ kappa_tmul F x a) hy
  refine (Subring.closure_le.2 ?_) h
  rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
  · obtain ⟨r, hr⟩ := x.2
    exact Subring.subset_closure (Or.inl ⟨r, by show (x : L) ⊗ₜ _ = _; rw [← hr]⟩)
  · exact Subring.subset_closure (Or.inr ⟨a.1, a.2, rfl⟩)

end Lemmas

theorem exists_open_cong : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ),
    0 < N → ∃ O : Set (finU L n), IsOpen O ∧ (1 : finU L n) ∈ O ∧
      ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  intro L _ _ _ n F N hN
  set c : Af L := algebraMap L (Af L) (N : L)⁻¹ with hc
  let S : Set (Af L) := {z | z * c ∈ Formalism.UG.intAd L}
  have hI : IsOpen ((Formalism.UG.intAd L : Subring (Af L)) : Set (Af L)) :=
    RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring _)
  have hS : IsOpen S := hI.preimage (continuous_id.mul continuous_const)
  let f : Fin n → Fin n → finU L n → Af L := fun s t k ↦
    pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) -
      pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t)
  have hm : Continuous (fun k : finU L n ↦ (((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hp : Continuous (pFin L) := continuous_snd
  have hf : ∀ s t, Continuous (f s t) := fun s t ↦
    (hp.comp (hm.matrix_elem s t)).sub continuous_const
  refine ⟨{k | ∀ s t, f s t k ∈ S}, ?_, ?_, ?_⟩
  · have e : {k | ∀ s t, f s t k ∈ S} = ⋂ s, ⋂ t, (f s t) ⁻¹' S := by ext; simp
    rw [e]
    exact isOpen_iInter_of_finite fun s ↦ isOpen_iInter_of_finite fun t ↦ hS.preimage (hf s t)
  · intro s t
    have e : f s t 1 = 0 := by simp [f]
    show f s t 1 * c ∈ Formalism.UG.intAd L
    rw [e, zero_mul]
    exact zero_mem _
  · intro k hk x hx
    have hloc : ∀ s t, F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      refine FiniteAdeleRing.ext _ fun w ↦ ?_
      rw [← F.loc x w s t, hx]
      rfl
    have hone : ∀ s t, F.κ ((1 : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      by_cases h : s = t <;> simp [Matrix.one_apply, h]
    have key : ∀ s t, ∃ y ∈ ALint L, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
        (1 : Matrix (Fin n) (Fin n) (AL L)) s t = (N : AL L) * y := by
      intro s t
      have h1 : f s t k * c ∈ Formalism.UG.intAd L := hk s t
      have hz : F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
          (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = f s t k := by
        simp only [f, map_sub, hloc, hone]
      refine ⟨F.κ.symm (f s t k * c), mem_ALint_of_kappa F (by rw [RingEquiv.apply_symm_apply]; exact h1), ?_⟩
      apply F.κ.injective
      rw [hz, map_mul, RingEquiv.apply_symm_apply, map_natCast, mul_comm (f s t k), ← mul_assoc, hc,
        ← map_natCast (algebraMap L (Af L)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'),
        map_one, one_mul]
    have hU : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t ∈ ALint L := by
      intro s t
      obtain ⟨y, hy, e⟩ := key s t
      rw [sub_eq_iff_eq_add] at e
      rw [e]
      refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
      by_cases h : s = t
      · simp [Matrix.one_apply, h, one_mem]
      · simp [Matrix.one_apply, h, zero_mem]
    exact ⟨hU, key⟩

end GlobalTheory.CongOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryRationalMatrixOfFirstPresentationPo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix

namespace GlobalTheory.RatPtsBridge

theorem exists_ratGL : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  intro L _ _ _ n γQ
  obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γQ.2)
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := hγ₀
  have h1 : conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) *
      (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := mul_eq_one_comm.1 h0
  have hmem : ratGL L n γ₀ ∈ UA L n := by
    show Formalism.UG.cT (conjAd L) ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
      ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1
    have e : Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) =
        (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map (algebraMap L (Ad L)) := by
      ext i j
      simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) * 1 *
      (γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) = 1
    rw [mul_one, e, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨ratGL L n γ₀, hmem⟩, γ₀, rfl, ?_⟩
  rw [← he]
  rfl

end GlobalTheory.RatPtsBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end

