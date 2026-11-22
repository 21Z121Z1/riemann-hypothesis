import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker Complex Classical
open Formalism.L2.Th1.H (matH alphaQ qOf opU slice pow4)
open scoped BigOperators ComplexConjugate Real

namespace WeilVac

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kappa_ne_zero {γ₀ : IsoK D} (k : KapChoice γ₀) : k.kappa ≠ 0 := by
  refine finprod_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => zpow_ne_zero _ ?_
  intro h0
  have h1 := k.rt_pow p p.2.1 p.2.2
  have hpi : k.pi p ≠ 0 := by
    intro h
    have h2 := k.pi_gen p p.2.1 p.2.2
    rw [h, Ideal.span_singleton_zero] at h2
    exact pow_ne_zero _ (k.pp p).ne_bot h2
  have hE : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by simpa using hpi
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne_zero _))] at h1
  exact div_ne_zero ((map_ne_zero _).2 hE) ((map_ne_zero _).2 ((map_ne_zero _).2 hE)) h1.symm

theorem thMM_spec (B : Base D cc δ) (h : B.StdOK) : B.IsThMM B.thMM ∧ B.thMM ≠ 0 := by
  obtain ⟨e, u⟩ := ThetaVec.thetaVector _ _ _ _ _ _ _ _ h _ (kappa_ne_zero B.kc)
  have h1 : B.IsThMM B.thMM := Classical.epsilon_spec (p := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa) e
  exact ⟨h1, (u _ h1.1 h1.2).1⟩

theorem thZero_ne_zero (B : Base D cc δ) (h : B.StdOK) (N N' : ℕ) : B.thZero N N' ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 (thMM_spec B h).2
  refine Function.ne_iff.2 ⟨fun τ _ _ => a τ, ?_⟩
  show ∏ _i : Fin N', ∏ _j : Fin N, B.thMM a ≠ 0
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => ha

theorem areaOK (B : Base D cc δ) : B.AreaOK := by
  rw [Base.AreaOK, ThetaVec.area_eq]
  exact GlobalTheory.OddTheta.area_eq B.L _ fun z => by rw [← B.lat]; rfl

theorem q_int (B : Base D cc δ) (h : B.StdOK) {x : D.what₂.Tau → ℂ} (hx : x ∈ B.lamM) :
    ∃ m : ℤ, qOf B.cq (matH (hOne B.L D.what₂.Tau)) x = m := by
  have hs : ∀ a, slice a (0 : Fin 4 × D.what₂.Tau → ℂ) = 0 := fun _ => rfl
  have h1 := h.betaSemi.1 (B.gC (ThetaVec.ins 0 x)) ⟨ThetaVec.ins 0 x, fun a => by
    rw [ThetaVec.slice_ins]; split_ifs; exacts [hx, B.lamM.zero_mem], rfl⟩
  rw [h.betaAlpha, ← mul_self_eq_one_iff] at h1
  simp only [ThetaVec.slice_ins, Fin.prod_univ_four, hs, h.alpha0, Fin.isValue, if_true, Fin.reduceEq, if_false,
    mul_one] at h1
  rw [alphaQ, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  have : (qOf B.cq (matH (hOne B.L D.what₂.Tau)) x : ℂ) = m := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination hm
  exact_mod_cast this

theorem entry_mem (B : Base D cc δ) {N N' : ℕ} {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) (stdL D N) (stdL D N')) : x ∈ powLat B.lamM N N' := by
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩ i j
  exact AddSubgroup.subset_closure ⟨w, hw, A i j, (GlobalTheory.OddGenus.mem_iff_entries D N N' A).1 hA i j, rfl⟩

theorem Hf_eq (B : Base D cc δ) {N N' : ℕ} (z w : VC D N N') :
    Hf D (tor0 D cc δ) z w =
      ∑ i, ∑ j, matH (hOne B.L D.what₂.Tau) (fun τ => z τ i j) (fun τ => w τ i j) := by
  have hA : area (tor0 D cc δ).abelian₂ = latticeArea B.L := (areaOK B).trans (ThetaVec.area_eq _)
  have e : ∀ u v : D.what₂.Tau → ℂ, matH (hOne B.L D.what₂.Tau) u v =
      ∑ τ, u τ * conj (v τ) / (latticeArea B.L : ℂ) := fun u v => ThetaVec.stdH_apply B.L u v
  simp only [e, Hf, hA, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem thZero_mem (B : Base D cc δ) (h : B.StdOK) (N N' : ℕ) :
    B.thZero N N' ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') := by
  have hθ := (thMM_spec B h).1.1
  refine ⟨?_, fun x hx z => ?_⟩
  · have hd : Differentiable ℂ B.thMM := differentiableOn_univ.1 hθ.1.differentiableOn
    unfold Base.thZero tensPow
    fun_prop
  · have hx' := entry_mem B hx
    choose m hm using fun i j => q_int B h (hx' i j)
    have h1 : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = ((∑ i, ∑ j, m i j : ℤ) : ℝ) := by
      rw [Hf_eq B]
      push_cast
      simp only [Complex.re_sum, Finset.mul_sum, ← hm]
      rfl
    have h2 : al D (tor0 D cc δ) x = ∏ i, ∏ j, alphaQ B.cq (matH (hOne B.L D.what₂.Tau)) fun τ => x τ i j := by
      rw [al, h1, round_intCast, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      simp only [alphaQ, hm, ← Complex.exp_sum, ← Finset.mul_sum]
      congr 1
      push_cast
      ring
    rw [h2, U, Hf_eq B, Hf_eq B]
    simp only [Base.thZero, tensPow, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hθ.2 _ (hx' i j) fun τ => z τ i j

def trivChar (D : D7) {N : ℕ} (hN : Even N) : HeckeU D N where
  f := 1
  n := fun _ => 0
  unitary := fun _ => by simp
  cont := ⟨1, one_pos, fun _ _ _ => rfl⟩
  aut := fun _ => by simp
  norm := fun _ => rfl
  par := fun _ => by simpa using hN
  unr := fun _ _ _ => rfl

end WeilVac

open WeilVac

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteClassFinite

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable abbrev sig : L →ₐ[maximalRealSubfield L] L :=
  ((IsCMField.complexConj L : L ≃ₐ[maximalRealSubfield L] L) : L →ₐ[maximalRealSubfield L] L)

noncomputable def swapAd : ReciprocityTheory.Aut.AL L ≃ₐ[maximalRealSubfield L]
    TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L :=
  Algebra.TensorProduct.comm _ _ _

theorem flip_symm_tmul (a : L) (b : Af (maximalRealSubfield L)) : (swapAd L).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

theorem flip_conj (x : ReciprocityTheory.Aut.AL L) :
    swapAd L (ReciprocityTheory.Aut.conjAL L x) = sigR (Af (maximalRealSubfield L)) (sig L) (swapAd L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def flipGL (n : ℕ) : GL (Fin n) (ReciprocityTheory.Aut.AL L) ≃*
    GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  Units.mapEquiv (swapAd L).toRingEquiv.mapMatrix.toMulEquiv

theorem JR_one (n : ℕ) : JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  unfold JR
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_GA_iff {n : ℕ} (g : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
    g ∈ ReciprocityTheory.Aut.GA L n ↔
      flipGL L n g ∈ HR (Af (maximalRealSubfield L)) (sig L) (1 : Matrix (Fin n) (Fin n) L) := by
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))
  have hc : Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map (swapAd L) := by
    ext i j; simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, flip_conj]
  change M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 ↔
    Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) *
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) * M.map (swapAd L) =
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L)
  rw [hc, JR_one, mul_one]
  have key : ∀ X Y : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L),
      X.map (swapAd L) * Y.map (swapAd L) = (X * Y).map (swapAd L) := fun X Y =>
    (map_mul (swapAd L).toRingEquiv.mapMatrix X Y).symm
  rw [key, mul_eq_one_comm]
  constructor
  · intro h; rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro h
    apply (swapAd L).toRingEquiv.mapMatrix.injective
    rw [map_one]; exact h

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

abbrev Jn (n : ℕ) : Matrix (Fin n) (Fin n) L := 1

abbrev Hf (n : ℕ) := HA (Af (maximalRealSubfield L)) (sig L) (Jn L n)

noncomputable def back (n : ℕ) : Hf L n →* Formalism.AUTREP.GAf L n where
  toFun h := ⟨(flipGL L n).symm (HA.mat _ _ _ h), by
    rw [mem_GA_iff, MulEquiv.apply_symm_apply]; exact h.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (flipGL L n).symm
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (flipGL L n).symm (HA.mat _ _ _ x) (HA.mat _ _ _ y)

noncomputable def fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : Hf L n :=
  ⟨flipGL L n g.1, (mem_GA_iff L g.1).1 g.2⟩

theorem back_fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : back L n (fwd L n g) = g := by
  apply Subtype.ext
  exact MulEquiv.symm_apply_apply (flipGL L n) g.1

theorem back_smul (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) (h : Hf L n) :
    back L n (γ • h) = back L n γ.1 * back L n h := by
  apply Subtype.ext
  exact map_mul (flipGL L n).symm (γ.1.1) (HA.mat _ _ _ h)

theorem back_mem_GQ (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) :
    back L n γ.1 ∈ ReciprocityTheory.Aut.GQ L n := by
  obtain ⟨γ0, hγ0, e⟩ := γ.2
  rw [ReciprocityTheory.Aut.GQ, Subgroup.mem_subgroupOf]
  refine ⟨γ0, ?_, ?_⟩
  · change (γ0 : Matrix (Fin n) (Fin n) L) * ReciprocityTheory.Aut.conjT _ (γ0 : Matrix (Fin n) (Fin n) L) = 1
    have h0 : Formalism.UG.cT (sig L : L →+* L) (γ0 : Matrix (Fin n) (Fin n) L) * 1 * (γ0 : Matrix (Fin n) (Fin n) L) = 1 := hγ0
    rw [mul_one] at h0
    rw [mul_eq_one_comm]
    exact h0
  · apply Units.ext
    have e' : Units.val (γ.1.1 : GL (Fin n) _) =
        Units.val (Formalism.UG.bc (inclR (F := ↥(maximalRealSubfield L)) (E := L) (Af (maximalRealSubfield L))) γ0) := by
      rw [e]; rfl
    change ((γ0 : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom =
      ((γ.1.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (swapAd L).symm
    rw [e']
    ext i j
    rfl

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def intSet : Set (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  (swapAd L).symm ⁻¹' (ReciprocityTheory.Aut.ALint L : Set (ReciprocityTheory.Aut.AL L))

theorem isOpen_intSet : IsOpen (intSet L) := by
  classical
  let b0 := Module.finBasisOfFinrankEq (maximalRealSubfield L) L
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L) (Finset.univ.image b0)
  let b := b0.unitsSMul (fun _ => Units.mk0 ((y : maximalRealSubfield L)) (by exact_mod_cast hy0))
  have hb : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply]
    have := hy _ (Finset.mem_image_of_mem b0 (Finset.mem_univ i))
    simpa [Units.smul_def, Int.cast_smul_eq_zsmul] using this
  let B := Algebra.TensorProduct.basis (Af (maximalRealSubfield L)) b
  haveI : IsModuleTopology (Af (maximalRealSubfield L))
      (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) := ⟨rfl⟩
  have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  let H : AddSubgroup (Fin 2 → Af (maximalRealSubfield L)) :=
    (ReciprocityTheory.Aut.ALint L).toAddSubgroup.comap
      ((swapAd L).symm.toRingEquiv.toAddMonoidHom.comp B.equivFun.symm.toLinearMap.toAddMonoidHom)
  have hW := GlobalTheory.AdLat.OpenLat.isOpen_integral (maximalRealSubfield L)
  have hV : (Set.univ.pi fun _ : Fin 2 => {a : Af (maximalRealSubfield L) |
      ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield L) v}) ⊆ H := by
    intro c hc'
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq] at hc'
    change (swapAd L).symm (B.equivFun.symm c) ∈ ReciprocityTheory.Aut.ALint L
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, flip_symm_tmul]
    have : b i ⊗ₜ[maximalRealSubfield L] c i =
        (b i ⊗ₜ[maximalRealSubfield L] (1 : Af (maximalRealSubfield L))) * (1 ⊗ₜ c i) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨b i, hb i⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨c i, hc' i, rfl⟩))
  have hHo : IsOpen (H : Set (Fin 2 → Af (maximalRealSubfield L))) := by
    apply AddSubgroup.isOpen_of_mem_nhds H (g := 0)
    apply Filter.mem_of_superset _ hV
    apply (isOpen_set_pi Set.finite_univ fun _ _ => hW).mem_nhds
    intro i _ v
    simp
  have : intSet L = B.equivFun ⁻¹' H := by
    ext x
    simp [intSet, H]
  rw [this]
  exact hHo.preimage hc

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def Kmax (n : ℕ) : Subgroup (Hf L n) := (ReciprocityTheory.Aut.Umax L n).comap (back L n)

theorem isOpen_Kmax (n : ℕ) : IsOpen (Kmax L n : Set (Hf L n)) := by
  refine ⟨{x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
    ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L}, ?_, ?_⟩
  · have : {x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
        ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L} =
        ⋂ i, ⋂ j, (fun x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) =>
          (x : Matrix (Fin n) (Fin n) _) i j) ⁻¹' intSet L := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intSet L).preimage ((Units.continuous_val (M := Matrix (Fin n) (Fin n)
        (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L))).matrix_elem i j)
  · ext h
    rfl

theorem herm_one (n : ℕ) : IsHermND (sig L) (Jn L n) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_finset_double_cosets_Umax (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n,
      ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n),
        t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes _ L (sig L)
    (GlobalTheory.AdelicU.isCMExt_of_isCMField L) n (Jn L n) (herm_one L n) (Kmax L n) (isOpen_Kmax L n)
  refine ⟨S.image (back L n), fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, e⟩ := hS (fwd L n g)
  refine ⟨⟨back L n γ.1, back_mem_GQ L n γ⟩, back L n s, back L n k,
    Finset.mem_image_of_mem _ hs, hk, ?_⟩
  have := congrArg (back L n) e
  rw [back_fwd, back_smul, map_mul, ← mul_assoc] at this
  exact this

end GlobalTheory.DefiniteClassFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameFunctionActionHolomorphicExtremalLowestStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), IsHolFam (fun _ => allPos n) fockL (vact lam) ∧ IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧ (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  first | exact @GlobalTheory.JointHarm.vact_isHolFam_isBotFam | exact GlobalTheory.JointHarm.vact_isHolFam_isBotFam | (intros; apply GlobalTheory.JointHarm.vact_isHolFam_isBotFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.HeckeExp

variable {D : D7}

open Classical in

theorem exists_idele_at {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1,
      by rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := by
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul, sub_self]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one,
      sub_eq_zero]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem arg_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    θ (infPart D (x : AE D)) / (‖θ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
  have h : θ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map θ).ne_zero
  exact div_ne_zero h (by exact_mod_cast norm_ne_zero_iff.2 h)

theorem eq_of_zpow_eq {n m : ℤ} (h : ∀ w : ℂ, ‖w‖ = 1 → w ^ n = w ^ m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h1 := h (Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have h2 : Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I) ^ (n - m) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hd' : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have e : ((n - m : ℤ) : ℂ) * (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast]; field_simp
  rw [← Complex.exp_int_mul, e, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem hasInfExp_unique {χ : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ τ a') :
    a = a' := by
  obtain ⟨n, hn, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  have e : n = m := eq_of_zpow_eq fun w hw => by
    obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w (by rintro rfl; simp at hw)
    have ho : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' hτ => by rw [hx2, if_neg hτ]
    have e1 := h1 θ hθ x hx1 ho
    have e2 := h2 θ hθ x hx1 ho
    rw [hx2, if_pos rfl, hw, Complex.ofReal_one, div_one] at e1 e2
    exact e1.symm.trans e2
  subst e
  linarith

theorem hasInfExp_mul {χ χ' : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ' τ a') :
    HasInfExp D (χ * χ') τ (a + a') := by
  obtain ⟨n, hn, h0, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hτ, h2 θ hθ x hx hτ, zpow_add₀ (arg_ne_zero _ x)]

theorem hasInfExp_inv {χ : IdC D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) : HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hτ, _root_.zpow_neg]

def hcSubgroup (D : D7) : Subgroup (IdC D) where
  carrier := {χ | IsHC D χ}
  one_mem' := isHC_one D
  mul_mem' := fun {χ χ'} h h' =>
    ⟨⟨h.1.1.mul h'.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => (h'.2 τ).elim fun _ ha' => ⟨_, hasInfExp_mul ha ha'⟩⟩
  inv_mem' := fun {χ} h =>
    ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2, inv_one]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => ⟨_, hasInfExp_inv ha⟩⟩

theorem hecke_exp_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧
    (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧
    ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') :=
  fun D => ⟨⟨hcSubgroup D, fun _ => Iff.rfl⟩, fun _ _ _ _ => hasInfExp_unique, fun _ _ _ _ _ => hasInfExp_mul⟩

end GlobalTheory.Mem.HeckeExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem isCuspFun_closed : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  intro D V φ φ' h h' c c'
  refine ⟨?_, fun a r C hC μ 𝓕 hμ h𝓕 g => ?_, fun k r C hC μ 𝓕 hμ h𝓕 g => ?_, fun r C hC μ 𝓕 hμ h𝓕 g => ?_⟩
  · refine (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + φ') (h.cont.add h'.cont) fun γ hγ g => ?_).2
      (add_mem ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c)
        ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ' h'.cont h'.left).1 c'))
    rw [Pi.add_apply, Pi.add_apply, h.left γ hγ, h'.left γ hγ]
  · simp only [Pi.smul_apply]
    rw [integral_smul, c r C hC μ 𝓕 hμ h𝓕 g, smul_zero]
  · simp only [rTr, mul_assoc]
    exact c r C hC μ 𝓕 hμ h𝓕 (g * k)
  · have e := integral_conj (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun n : NI V C => φ ((n : GA D V) * g))
    rw [c r C hC μ 𝓕 hμ h𝓕 g, map_zero] at e
    exact e

end GlobalTheory.Mem.Th
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActioStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : GL (Fin M) (AF F ⊗[F] E)) (γ : GL (Fin n) (AF F ⊗[F] E)), IsProd b ν mi mv → IsProd b (ν.map (lrAct g.val γ.val)) (mi.map (lrAct (g.val.map prInf) (γ.val.map prInf))) (fun v => (mv v).map (lrAct (g.val.map (prV v)) (γ.val.map (prV v)))) := by
  first | exact @GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct | exact GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct | (intros; apply GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZerosStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), (k : ℕ) + 1 = D.R.m → n = D.R.r + k * D.R.t → N = n + D.R.t → IsEnum (parB (Ptw D) k τ) lam ε → IsEnum (parB (Ptw D) D.R.m τ) lam' ε' → ε = allPos n ∧ ε' = allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = expS D k τ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + expT D k τ) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (allPos N) lam' b = -(x₁ : ℝ) - ν (Fin.rev b) := by
  first | exact @GlobalTheory.LastStepParam.lastStep_param | exact GlobalTheory.LastStepParam.lastStep_param | (intros; apply GlobalTheory.LastStepParam.lastStep_param <;> assumption)
end

