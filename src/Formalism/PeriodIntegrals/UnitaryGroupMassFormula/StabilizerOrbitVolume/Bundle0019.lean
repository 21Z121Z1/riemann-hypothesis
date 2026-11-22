import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0013

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfFS
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def SemisimpleTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → IsSemisimpleRing (Ainf F ⊗[F] E)

theorem exists_dual_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) (c : Fin a → K) :
    ∃ w : Fin M → K, ∀ i, ∑ k, Z i k * w k = c i := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k => ∑ i', c i' * p (Pi.single k 1) i', fun i => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * ∑ i', c i' * p (Pi.single k 1) i' =
      ∑ i', c i' * (p (Z i)) i' := by
    conv_rhs => rw [hZi]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => by ring
  rw [e1, ← hι, hp]
  simp [Pi.single_apply]

theorem freeSurj_of (h : SemisimpleTens) : FreeSurj := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX S
  have := h F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E := fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

theorem densInf_of_ss (h2 : TensR) (h3 : SemisimpleTens) : DensInf :=
  densInf_of_tens h2 (freeSurj_of h3)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCore
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def GramFilt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
      (x : Fin a → Fin M → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) x →
      ∃ N ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ y, y - x ∈ N →
        ∀ Λ0, scaledB (Fv F v) (latSub b v a M) Λ0 →
          (Λ0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ⊆ N →
        ∃ (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
          (H : ℕ → AddSubgroup (HermR (Fv F v) σ a))
          (D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a),
          Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
          (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
          (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
          (∀ n, (Λ n).map D = H n) ∧
          ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ hσ J hJ (y + Z + W) - gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈
              H (n + 1)

theorem densVLat_of (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensVLat := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, t3, _t4, t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  intro d b x hx
  obtain ⟨N, hN, hd⟩ := hF F E σ hσ M J hJ.1 hJ.2 a h1 h2 v d b x hx
  refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
  subst h0
  exact densCos_of_filt hP1 hP2 μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (Continuous.subtype_mk t5 _) (fun _ => rfl) y Λ H hΛo hΛc hΛa
    hHo hHc hHb D hD hyp

theorem densV_of_filt (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensV :=
  densV_of_lat hT (densVLat_of hP1 hP2 hT hF)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDxSt
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def DxOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ)
      (b : Module.Basis (Fin d) F E) (x : Fin a → Fin M → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) x →
      IsOpen ((fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) '' (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E)))

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSecSt
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def SecGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (_hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (_hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (R : Type) [CommRing R] [Algebra F R], IsSemisimpleRing (R ⊗[F] E) →
    ∀ (a : ℕ) (x : Fin a → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) x →
      ∃ q : Fin M → Fin a → R ⊗[F] E, ∀ S : Matrix (Fin a) (Fin a) (R ⊗[F] E),
        S ∈ HermR R σ a →
        gramB R σ J x (fun j k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') = S

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmC
section
noncomputable section

namespace PI.VolStabSW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabSW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

section Crd

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {a M : ℕ}

def crdH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a × Fin M × Fin d → R) where
  toFun X c := crd b R (X c.1 c.2.1) c.2.2
  invFun Y x i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (x, i, k))
  left_inv X := by
    funext x i
    show (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => crd b R (X x i) k) = X x i
    have e : (fun k => crd b R (X x i) k) = (Algebra.TensorProduct.basis R b).equivFun (X x i) := by
      funext k
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    funext c
    show crd b R ((Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (c.1, c.2.1, k))) c.2.2
      = Y c
    have e : ∀ y, crd b R y c.2.2 = (Algebra.TensorProduct.basis R b).equivFun y c.2.2 := fun y => by
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_pi fun c =>
    (continuous_crd b R c.2.2).comp ((continuous_apply c.2.1).comp (continuous_apply c.1))
  continuous_invFun := continuous_pi fun x => continuous_pi fun i =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply _)

end Crd

section Split

variable (F : Type) [Field F] [NumberField F]

def splitH (ι : Type) : (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun Y := (fun c => fstA F (Y c), fun c => sndA F (Y c))
  invFun p c := pairA F (p.1 c) (p.2 c)
  left_inv Y := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_pi fun c => ?_).prodMk (continuous_pi fun c => ?_)
    · exact continuous_fst.comp (continuous_apply c)
    · exact continuous_snd.comp (continuous_apply c)
  continuous_invFun := continuous_pi fun c =>
    ((continuous_apply c).comp continuous_fst).prodMk ((continuous_apply c).comp continuous_snd)

end Split

section admitted

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}

def locBox (D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
  (crdH b (Fv F v)) ⁻¹' (Set.pi univ fun c => D c v)

variable {b}

theorem isClopen_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsClopen (locBox b D v) :=
  (show IsClopen (Set.pi univ fun c => D c v) from ⟨isClosed_set_pi (fun c _ => (hD.1 c v).1.isClosed),
    isOpen_set_pi finite_univ (fun c _ => (hD.1 c v).1.isOpen)⟩).preimage (crdH b (Fv F v)).continuous

theorem isCompact_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsCompact (locBox b D v) :=
  (crdH b (Fv F v)).isCompact_preimage.2 (isCompact_univ_pi fun c => (hD.1 c v).2)

theorem isSB_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) :
    IsSB ((locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_locBox hD v)).isLocallyConstant,
    HasCompactSupport.intro' (isCompact_locBox hD v) (isClopen_locBox hD v).isClosed
      fun Y hY => Set.indicator_of_notMem hY _⟩

theorem locBox_eq_latV {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by
  ext Y
  simp only [locBox, latV, mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · intro h x i k
    have h1 := h (x, i, k)
    rw [hv] at h1
    exact h1
  · intro h c
    rw [hv]
    exact h c.1 c.2.1 c.2.2

theorem finprod_ite {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by
  by_cases hall : ∀ v, P v
  · rw [if_pos hall]
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (hall v)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    refine finprod_eq_zero _ v0 (if_neg hv0) ?_
    refine (eventually_cofinite.1 h).subset fun v hv => ?_
    intro hP
    exact hv (if_pos hP)

theorem finprod_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by
  classical
  set q := crdH b (Af F) W
  have hv : ∀ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      if (∀ c, q c v ∈ D c v) then 1 else 0 := by
    intro v
    have e : ∀ c, crdH b (Fv F v) (projV v W) c = q c v := fun c =>
      crd_map b (evalV F v) (W c.1 c.2.1) c.2.2
    rw [Set.indicator_apply]
    simp only [locBox, mem_preimage, Set.mem_univ_pi, e, Pi.one_apply]
  rw [finprod_congr hv, finprod_ite _ ?_]
  · rw [Set.indicator_apply]
    by_cases hq : q ∈ boxS D
    · rw [if_pos hq, if_pos (fun v c => hq c v)]
      rfl
    · rw [if_neg hq, if_neg (fun h' => hq (fun c v => h' v c))]
  · filter_upwards [hD.2, eventually_all.2 fun c => (q c).eventually] with v h1 h2 c
    rw [h1 c]
    exact h2 c

end admitted

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {a M : ℕ}

variable (F E a M) in

def psiH : (Fin a → Fin M → AF F ⊗[F] E) ≃ₜ
    (Fin a × Fin M × Fin (Module.finrank F E) → Ainf F) ×
      (Fin a × Fin M × Fin (Module.finrank F E) → Af F) :=
  (crdH (Module.finBasis F E) (AF F)).trans (splitH F _)

theorem psiH_fst (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).1 = crdH (Module.finBasis F E) (Ainf F) (projInf X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (fstA F) (X c.1 c.2.1) c.2.2).symm

theorem psiH_snd (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).2 = crdH (Module.finBasis F E) (Af F) (projFin X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (sndA F) (X c.1 c.2.1) c.2.2).symm

theorem key_int (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2)
    {D : Fin a × Fin M × Fin (Module.finrank F E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (f : C_c(Fin a × Fin M × Fin (Module.finrank F E) → Ainf F, ℝ)) :
    ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν1 =
      ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν2 := by
  classical
  let b := Module.finBasis F E
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f (crdH b (Ainf F) Y) : ℝ) : ℂ)
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (locBox b D v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun W => ∏ᶠ v, Φv v (projV v W)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hadm : IsAdm F E Φ := by
    refine ⟨_, b, Φinf, Φf, Φv, ?_, ?_, ⟨fun v => isSB_locBox hD v, ?_, fun _ => rfl⟩, fun _ => rfl⟩
    · exact Complex.continuous_ofReal.comp (f.continuous.comp (crdH b (Ainf F)).continuous)
    · exact (f.hasCompactSupport.comp_homeomorph (crdH b (Ainf F))).comp_left Complex.ofReal_zero
    · filter_upwards [hD.2] with v hv
      exact congrArg (fun s => s.indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) (locBox_eq_latV v hv)
  have hΦ : ∀ X, Φ X = ((f (psiH F E a M X).1 *
      (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 : ℝ) : ℂ) := by
    intro X
    have e2 : Φf (projFin X) = (boxS D).indicator 1 ((psiH F E a M X).2) := by
      rw [psiH_snd]
      exact finprod_locBox hD (projFin X)
    simp only [Φ, e2, psiH_fst, Φinf, b]
    rw [Complex.ofReal_mul]
    congr 1
    by_cases hq : (psiH F E a M X).2 ∈ boxS D
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      simp
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
      simp
  have := h Φ hadm
  simp only [hΦ] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Main

end PI.VolStabSW.DeterminantAdmissible
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHC
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ) :
    AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
    ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [AddSubgroup.coe_add, Matrix.add_apply, map_add, Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k
    simp only [ZeroMemClass.coe_zero, Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [NegMemClass.coe_neg, Matrix.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

def VolAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
      (∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv → μv (latV b v) = 1) ∧
      (∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → νv (hermO b v σ a) = 1)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdAlt
section
namespace PI.VolStabSW

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabSW
end

