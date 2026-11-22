import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ParaLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem detDD_one (s : SplitPlace L) (r : ℕ) :
    NG.detDD s r (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  unfold NG.detDD
  have : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} =>
      ((1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem continuous_detDD (s : SplitPlace L) (r : ℕ) :
    Continuous (NG.detDD (n := n) s r) := by
  unfold NG.detDD
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))).matrix_elem a.1 b.1

section main
variable (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
  (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)

def paraSub (hP : NG.LevelPara J χ s r ξ) :
    Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) where
  carrier := {g | NG.ParaRT s r g}
  one_mem' := by
    have h := (hP.mem 1 (trivOutside_one _)).1 J.one_mem
    simpa using h
  mul_mem' := by
    intro g h hg hh
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
    have hxy := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
    rw [← map_mul]
    exact (hP.mem _ hxy).1 (J.mul_mem ((hP.mem x hx).2 hg) ((hP.mem y hy).2 hh))
  inv_mem' := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have hi := GlobalTheory.SatInd.CosetFin.trivOutside_inv hx
    show NG.ParaRT s r (s.loc n x)⁻¹
    rw [← map_inv]
    exact (hP.mem _ hi).1 (J.inv_mem ((hP.mem x hx).2 hg))

end main
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section main2
variable {s : SplitPlace L} {r : ℕ} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
  {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ}

def lift (s : SplitPlace L) (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : GAf L n :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose

theorem lift_triv (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    TrivOutside {s.v} (lift s g) :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.1

theorem loc_lift (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    s.loc n (lift s g) = g :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.2

theorem lift_mem (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : lift s g.1 ∈ J :=
  (hP.mem _ (lift_triv g.1)).2 (by rw [loc_lift]; exact g.2)

def thetaFun (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : ℂˣ :=
  χ ⟨lift s g.1, lift_mem hP g⟩

theorem chi_eq (hP : NG.LevelPara J χ s r ξ) (κ : GAf L n) (hκ : TrivOutside {s.v} κ) (hJ : κ ∈ J)
    (h : s.loc n κ ∈ paraSub s r J χ ξ hP) : χ ⟨κ, hJ⟩ = thetaFun hP ⟨s.loc n κ, h⟩ := by
  unfold thetaFun
  set κ₀ := lift s (s.loc n κ) with hκ₀
  have h0 : κ₀ ∈ J := lift_mem hP ⟨s.loc n κ, h⟩
  have ht : TrivOutside {s.v} (κ * κ₀⁻¹) :=
    GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (lift_triv _))
  have hl : s.loc n (κ * κ₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hκ₀, loc_lift, mul_inv_cancel]
  have hδ : κ * κ₀⁻¹ ∈ J := J.mul_mem hJ (J.inv_mem h0)
  have hc : χ ⟨κ * κ₀⁻¹, hδ⟩ = 1 := by
    rw [hP.chr _ hδ ht 1 (by rw [hl, detDD_one]; rfl), map_one]
  have hprod : (⟨κ, hJ⟩ : J) = ⟨κ * κ₀⁻¹, hδ⟩ * ⟨κ₀, h0⟩ := by
    apply Subtype.ext; simp
  rw [hprod, map_mul, hc, one_mul]

def theta (hP : NG.LevelPara J χ s r ξ) : paraSub s r J χ ξ hP →* ℂˣ where
  toFun := thetaFun hP
  map_one' := by
    have h1 : s.loc n (1 : GAf L n) ∈ paraSub s r J χ ξ hP := by rw [map_one]; exact (paraSub s r J χ ξ hP).one_mem
    have := chi_eq hP 1 (trivOutside_one _) J.one_mem h1
    have e : (⟨s.loc n 1, h1⟩ : paraSub s r J χ ξ hP) = 1 := by apply Subtype.ext; simp
    rw [e] at this
    rw [← this]
    exact map_one χ
  map_mul' := by
    intro g h
    set x := lift s g.1
    set y := lift s h.1
    have hx := lift_mem hP g
    have hy := lift_mem hP h
    have hxy : TrivOutside {s.v} (x * y) :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (lift_triv _) (lift_triv _)
    have hm : s.loc n (x * y) ∈ paraSub s r J χ ξ hP := by
      rw [map_mul, loc_lift, loc_lift]; exact (g * h).2
    have := chi_eq hP (x * y) hxy (J.mul_mem hx hy) hm
    have e : (⟨s.loc n (x * y), hm⟩ : paraSub s r J χ ξ hP) = g * h := by
      apply Subtype.ext; simp [x, y, loc_lift]
    rw [e] at this
    rw [← this]
    have e2 : (⟨x * y, J.mul_mem hx hy⟩ : J) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e2, map_mul]
    rfl

end main2
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel

theorem exists_parahoric_char : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  intro L _ _ _ n s r J χ ξ hP hξ
  obtain ⟨N, hN⟩ := hξ
  refine ⟨paraSub s r J χ ξ hP, theta hP, fun g => Iff.rfl, ?_, fun g hg => hg.1, ?_, ?_⟩
  · intro g h d hd
    show χ ⟨lift s g, lift_mem hP ⟨g, h⟩⟩ = ξ d
    exact hP.chr _ _ (lift_triv g) d (by rw [loc_lift]; exact hd)
  · apply Subgroup.isOpen_of_mem_nhds
    have hc : Continuous fun g : paraSub s r J χ ξ hP => NG.detDD s r g.1 :=
      (continuous_detDD s r).comp continuous_subtype_val
    have h1 : NG.detDD s r ((1 : paraSub s r J χ ξ hP) : GL (Fin n) _) = 1 := detDD_one s r
    obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
    set a : s.v.adicCompletion (maximalRealSubfield L) := ((π : maximalRealSubfield L) : s.v.adicCompletion (maximalRealSubfield L)) ^ N
    have ha : Valued.v a = WithZero.exp (-(N : ℤ)) := by
      simp only [a, map_pow, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
      congr 1; simp
    have ha0 : (Valued.v a) ≠ 0 := by rw [ha]; simp
    have hnhds : {x : s.v.adicCompletion (maximalRealSubfield L) |
        Valued.v (x - 1) < WithZero.exp (-(N : ℤ))} ∈ nhds (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict a) (by rwa [ne_eq, Valuation.restrict_eq_zero_iff]), ?_⟩
      intro y hy
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      rw [← ha]
      exact (Valuation.restrict_lt_iff _).1 hy
    have hpre := hc.tendsto 1 (by rw [h1]; exact hnhds)
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
    have hne : NG.detDD s r g.1 ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hg
      exact absurd hg (not_lt.2 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    have hθ : theta hP g = ξ (Units.mk0 _ hne) := by
      show χ ⟨lift s g.1, lift_mem hP g⟩ = _
      exact hP.chr _ _ (lift_triv g.1) _ (by rw [loc_lift]; rfl)
    show theta hP g = 1
    rw [hθ]
    exact hN _ (le_of_lt hg)
  · intro κ hκ hJ h
    exact chi_eq hP κ hκ hJ h

end GlobalTheory.ParaLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertLocalEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section
open TensorProduct

namespace GlobalTheory.InertLocSurj

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem compAt_conjAL (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [conjAL, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul,
      GlobalTheory.InertUmax.compAt_tmul, Formalism.UG.sigR, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add]; rw [ha, hb]

theorem exists_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (t : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ T : AL L, compAt L v T = t ∧ ∀ u, u ≠ v → compAt L u T = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, rfl⟩ := GlobalTheory.InertUmax.tensor_decomp b t
  refine ⟨b 0 ⊗ₜ GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same]
  · intro u hu
    rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n →
    ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  have hy' : Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let Z : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P * y * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)
  have hPP : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZ : Formalism.UG.cT Dv.σw Z * Z = 1 := by
    simp only [Z, Units.val_mul, Formalism.UG.cT_mul]
    have h1 := Dv.Panti
    calc Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) * Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) * (y : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _))
        = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) *
            (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
            (y : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          rw [h1, hy']
      _ = Formalism.UG.cT Dv.σw ((Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hZ' : Z * Formalism.UG.cT Dv.σw Z = 1 := mul_eq_one_comm.mp hZ
  set sg := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) with hsg
  let Xv : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    Z.map Dv.e.symm
  have hXZ : Xv.map Dv.e = Z := by ext i j; simp [Xv]
  have hX : Xv * conjT sg Xv = 1 := by
    have hcomm : ∀ z, Dv.e.symm (Dv.σw z) = sg (Dv.e.symm z) := by
      intro z
      apply Dv.e.injective
      rw [RingEquiv.apply_symm_apply, Dv.comm, RingEquiv.apply_symm_apply]
    have h2 := congrArg (fun M => M.map Dv.e.symm) hZ'
    simp only [Matrix.map_mul] at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h2
    convert h2 using 2
    ext i j
    simp [conjT, Formalism.UG.cT, Xv, hcomm]
  choose T hTv hTu using GlobalTheory.InertLocSurj.exists_supported (L := L) v
  obtain ⟨E, hEv, hEu⟩ := GlobalTheory.InertLocSurj.exists_supported (L := L) v 1
  let A : Matrix (Fin n) (Fin n) (AL L) := fun i j => T (Xv i j) + if i = j then 1 - E else 0
  have hAv : A.map (compAt L v) = Xv := by
    ext i j
    show compAt L v (T (Xv i j) + if i = j then 1 - E else 0) = Xv i j
    by_cases h : i = j
    · rw [if_pos h, map_add, hTv, map_sub, map_one, hEv, sub_self, add_zero]
    · rw [if_neg h, map_add, hTv, map_zero, add_zero]
  have hAu : ∀ u, u ≠ v → A.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    show compAt L u (T (Xv i j) + if i = j then 1 - E else 0) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_add, hTu _ u hu, map_sub, map_one, hEu u hu, zero_add, sub_zero]
    · rw [if_neg h, if_neg h, map_add, hTu _ u hu, map_zero, add_zero]
  have hmap : ∀ u, (A * conjT (conjAL L) A).map (compAt L u) =
      A.map (compAt L u) * conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
        (u.adicCompletion (maximalRealSubfield L))) (A.map (compAt L u)) := by
    intro u
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjT, GlobalTheory.InertLocSurj.compAt_conjAL]
  have hA : A * conjT (conjAL L) A = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have h3 : (A * conjT (conjAL L) A).map (compAt L u) = (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L u) := by
      rw [hmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rcases eq_or_ne u v with rfl | hu
      · rw [hAv]; exact hX
      · rw [hAu u hu, conjT_one, Matrix.one_mul]
    have h4 := congrFun (congrFun h3 i) j
    simp only [Matrix.map_apply] at h4
    rw [map_sub, h4, sub_self]
  let g : GL (Fin n) (AL L) := ⟨A, conjT (conjAL L) A, hA, mul_eq_one_comm.mp hA⟩
  have hg : g ∈ GA L n := hA
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hAu u (by simpa using hu)
  · have hbc : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) = Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      show (A.map (compAt L v)).map Dv.e = Z
      rw [hAv, hXZ]
    unfold InertDatum.loc
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) * Dv.P = y
    rw [hbc]
    group

end GlobalTheory.InertLocSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacua
section
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem sum_charSum_eq_card_filter {B ι M : Type} [AddCommGroup B] [Fintype B] [AddCommGroup M] [Module ℂ M]
    (Y : Finset ι) (x : ι) (hx : x ∈ Y) (χ : B → ι → ℂ)
    (hmul : ∀ b b', ∀ y ∈ Y, χ (b + b') y = χ b y * χ b' y) (hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0) (v : ι → M)
    [DecidablePred (fun y => ∀ b, χ b y = χ b x)] :
    ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y =
      (Fintype.card B : ℂ) • ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), v y := by
  have h0 : ∀ y ∈ Y, χ 0 y = 1 := by
    intro y hy
    have e := hmul 0 0 y hy
    rw [add_zero] at e
    exact mul_left_cancel₀ (hne 0 y hy) (by rw [mul_one]; exact e.symm)
  have key : ∀ y ∈ Y, ∑ b, (χ b x)⁻¹ * χ b y =
      if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0 := by
    intro y hy
    split_ifs with hP
    · simp [hP, inv_mul_cancel₀ (hne _ x hx)]
    · let φ : AddChar B ℂ :=
        { toFun := fun b => (χ b x)⁻¹ * χ b y
          map_zero_eq_one' := by simp [h0 x hx, h0 y hy]
          map_add_eq_mul' := by
            intro b b'
            show (χ (b + b') x)⁻¹ * χ (b + b') y = ((χ b x)⁻¹ * χ b y) * ((χ b' x)⁻¹ * χ b' y)
            rw [hmul b b' x hx, hmul b b' y hy, mul_inv]
            ring }
      have hφ : φ ≠ 1 := by
        intro h1
        apply hP
        intro b
        have e : φ b = 1 := by rw [h1, AddChar.one_apply]
        exact ((inv_mul_eq_one₀ (hne b x hx)).mp e).symm
      show ∑ b, φ b = 0
      exact AddChar.sum_eq_zero_of_ne_one hφ
  calc ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y = ∑ y ∈ Y, (∑ b, (χ b x)⁻¹ * χ b y) • v y := by
        simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]; exact Finset.sum_comm
    _ = ∑ y ∈ Y, (if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0) • v y :=
        Finset.sum_congr rfl (fun y hy => by rw [key y hy])
    _ = _ := by
        rw [Finset.smul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> simp

end GlobalTheory.Hk3.HoweG

namespace GlobalTheory.Hk3.HoweG

open GlobalTheory.Hk3

theorem gramClass_sum_mem_span_selfDual_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac x hx
  classical
  have hP' := hP
  obtain ⟨hU, hodd, hSint, hTint, hS, hT, hδ, hpsi_int, hpsi_ne, -, hρ, -, -, -⟩ := hP'
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix L ϖ σ q n n' JS JT hU hodd hSint hTint hS hT x hx
  obtain ⟨Y, hxY, hYA, hYd, B, _, _, b0, l, hb0, hl, hcov, hmul, hsep⟩ :=
    GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group L ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ⟨ha1, ha2, ha3, ha4⟩
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ y u, u ∈ HoweDuality.intMat L n' n →
      ρ (y + u) s = ψ (-((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2)) • ρ y s := by
    intro y u hu
    have h1 : ρ y s = ψ ((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2) • ρ (y + u) s := by
      have := congrArg (fun f => f s) (hρ y u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  set χ : B → Matrix (Fin n') (Fin n) L → ℂ :=
    fun b y => ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) with hχ
  have hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0 := by
    intro b y _ h0
    have := hψinv (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2))
    rw [show ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = χ b y from rfl, h0,
      zero_mul] at this
    exact zero_ne_one this
  set Spn := Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} with hSpn

  have hvacb : ∀ b, ∑ y ∈ Y, χ b y • ρ y s ∈ Spn := by
    intro b
    have hinj : Set.InjOn (fun y => y + l b y) Y := by
      intro y hy y' hy' e
      refine hYd y hy y' hy' ?_
      have e' : y - y' = l b y' - l b y := by
        have := congrArg (fun z => z - l b y - y') e
        simp only at this
        rw [show y + l b y - l b y - y' = y - y' by abel, show y' + l b y' - l b y - y' = l b y' - l b y by abel] at this
        exact this
      rw [e']
      exact (HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1
    have hsum : ∑ y ∈ Y, χ b y • ρ y s = ∑ z ∈ Y.image (fun y => y + l b y), ρ z s := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun y hy => (hshift y (l b y) (hl b y hy).1).symm)
    rw [hsum]
    refine Submodule.subset_span ⟨b0 b, hb0 b, ?_⟩
    refine GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac (b0 b) (hb0 b) _ ?_ ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (hl b y hy).2
    · intro z hz z' hz' hzz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      have : y = y' := by
        refine hYd y hy y' hy' ?_
        have e : y - y' = (y + l b y - (y' + l b y')) + (l b y' - l b y) := by abel
        rw [e]
        exact (HoweDuality.intMat L n' n).add_mem hzz
          ((HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1)
      rw [this]
    · intro u hu
      obtain ⟨y, hy, hm⟩ := hcov b u hu
      exact ⟨y + l b y, Finset.mem_image_of_mem _ hy, hm⟩
  have hF := sum_charSum_eq_card_filter Y x hxY χ hmul hne (fun y => ρ y s)
  have hcard : (Fintype.card B : ℂ) ≠ 0 := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this.ne'
  refine ⟨Y.filter (fun y => ∀ b, χ b y = χ b x), fun _ => 1, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hxY, fun _ => rfl⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨one_ne_zero, hYA y hy1, (hsep y hy1).mpr hy2⟩
  · intro y hy y' hy' hne' hm
    exact hne' (hYd y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hm)
  · simp only [one_smul]
    have e : ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), ρ y s =
        (Fintype.card B : ℂ)⁻¹ • ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • ρ y s := by
      rw [hF, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvacb b))

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeUnramified_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  first | exact @GlobalTheory.Hk3.howe_all_vacua | exact GlobalTheory.Hk3.howe_all_vacua | (intros; apply GlobalTheory.Hk3.howe_all_vacua <;> assumption)
end

