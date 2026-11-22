import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0006
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix

section Bases

variable (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (M : ℕ)
  (A : Type) [CommRing A] [Algebra F A]

def bV : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) F (Fin M → E) :=
  (Pi.basis fun _ : Fin M => Module.finBasis F E).reindex (Fintype.equivFin _)

def bVR : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) A
    (Fin M → A ⊗[F] E) :=
  (Pi.basis fun _ : Fin M => Algebra.TensorProduct.basis A (Module.finBasis F E)).reindex
    (Fintype.equivFin _)

theorem bVR_apply (i : Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) :
    bVR F E M A i = ratV (F := F) A (bV F E M i) := by
  rw [bVR, bV, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  generalize (Fintype.equivFin (Σ _ : Fin M, Fin (Module.finrank F E))).symm i = p
  obtain ⟨a, c⟩ := p
  funext j
  simp only [Pi.basis_apply, Algebra.TensorProduct.basis_apply, Formalism.L2.SG.Sub.ratV]
  by_cases hj : j = a
  · subst hj
    simp only [Pi.single_eq_same]
    first | rfl | simp
  · simp only [Pi.single_eq_of_ne hj]
    first | rfl | simp

end Bases

theorem vMod_of (hO : OrthInv) (hB : TraceBase) (hN : TraceGramND) : VMod := by
  intro F E _ _ _ _ _ σ hCM M J hJ g μ hμ
  classical
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : FiniteDimensional F E := Lc.finite_nf F E
  obtain ⟨htr, ht2R, hlcR, hscR⟩ := Lc.tensor_adele_topology_holds F E
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M (AF F)
  set e : (Fin M → AF F ⊗[F] E) ≃ₗ[AF F] (Fin k → AF F) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := AF F) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) _
  let ec : (Fin M → AF F ⊗[F] E) ≃ₜ+ (Fin k → AF F) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → AF F) →ₗ[AF F] (Fin k → AF F) :=
    e.toLinearMap ∘ₗ ((lin (AF F) σ J g).restrictScalars (AF F)) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin (AF F) σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F (AF F))
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F (AF F) G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (hN F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, hB F E (AF F) σ M J]
    rfl
  have key : ∀ x y : Fin k → AF F, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → AF F, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := hO F k G X hGu hXG μ' hμ'
  have hlin : (lin (AF F) σ J g : (Fin M → AF F ⊗[F] E) → (Fin M → AF F ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → AF F ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModDefs
section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r)

def Wsub : AddSubgroup (Fin M → R ⊗[F] E) where
  carrier := {w | (∀ a, hR R σ J (ratV (F := F) R (P.e a)) w = 0) ∧
    (∀ a, hR R σ J (ratV (F := F) R (P.f a)) w = 0) ∧ hR R σ J (ratV (F := F) R P.z) w = 0}
  zero_mem' := by
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;> simp [hR, Formalism.UG.hform]
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have hadd : ∀ u x y : Fin M → R ⊗[F] E, hR R σ J u (x + y) = hR R σ J u x + hR R σ J u y :=
      fun u x y => (PG.Dat.hL (datR R σ J P (1 : F)) u).map_add x y
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [hadd, hx1, hy1, add_zero]
    · rw [hadd, hx2, hy2, add_zero]
    · rw [hadd, hx3, hy3, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : ∀ u : Fin M → R ⊗[F] E, hR R σ J u (-x) = -hR R σ J u x := fun u => by
      simp [hR, Formalism.UG.hform, Finset.sum_neg_distrib]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [hneg, hx1, neg_zero]
    · rw [hneg, hx2, neg_zero]
    · rw [hneg, hx3, neg_zero]

def Sk (r : ℕ) : AddSubgroup (Fin r → Fin r → R ⊗[F] E) where
  carrier := {c | ∀ a b, c a b + sigR R σ (c b a) = 0}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro x y hx hy a b
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [add_add_add_comm, hx a b, hy a b, add_zero]
  neg_mem' := by
    intro x hx a b
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, map_neg] at *
    rw [← neg_add, hx a b, neg_zero]

def betaM (w w' : Fin r → Fin M → R ⊗[F] E) : Fin r → Fin r → R ⊗[F] E := fun a b =>
  inclR (F := F) R (1 / 2 : E) * (hR R σ J (w' a) (w b) - hR R σ J (w a) (w' b))

end Gen

def HeisenbergCoordinates : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∃ Φ : FrameUnipotentSubgroup (AF F) σ J P ≃ₜ ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r),
      (∀ n₀ n : FrameUnipotentSubgroup (AF F) σ J P,
        (fun a => ((Φ (n₀ * n)).1 a : Fin M → AF F ⊗[F] E)) =
          (fun a => ((Φ n₀).1 a : Fin M → AF F ⊗[F] E) + ((Φ n).1 a : Fin M → AF F ⊗[F] E)) ∧
        ((Φ (n₀ * n)).2 : Fin r → Fin r → AF F ⊗[F] E) =
          ((Φ n₀).2 : Fin r → Fin r → AF F ⊗[F] E) + ((Φ n).2 : Fin r → Fin r → AF F ⊗[F] E) +
            betaM (AF F) σ J (fun a => ((Φ n₀).1 a : Fin M → AF F ⊗[F] E))
              (fun a => ((Φ n).1 a : Fin M → AF F ⊗[F] E))) ∧
      (∀ h ∈ Hsub (AF F) σ J P, ∀ n n' : FrameUnipotentSubgroup (AF F) σ J P,
        (n' : HA (AF F) σ J) = h * n * h⁻¹ →
        (∀ a, ((Φ n').1 a : Fin M → AF F ⊗[F] E) = lin (AF F) σ J h ((Φ n).1 a)) ∧
          (Φ n').2 = (Φ n).2)

theorem lin_mem_Wsub {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
    {P : Frame E M r} {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ Wsub R σ J P) : lin R σ J h w ∈ Wsub R σ J P := by
  have hS := heisenberg_le_stabilizer R σ J P hh
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · rw [← stabilizer_fixes_frame_vector R σ J P hS a, hR_lin]; exact h1 a
  · have := hh
    rw [Hsub, mem_stabT] at this
    have hf := this (Fin.natAdd (r + 1) a)
    rw [tupH_f] at hf
    rw [← hf, hR_lin]; exact h2 a
  · rw [← stabilizer_fixes_normal_vector hS, hR_lin]; exact h3

def actW {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
    {P : Frame E M r} {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : Wsub R σ J P) :
    Wsub R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wsub hh w.2⟩

def WMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ (h : HA (AF F) σ J) (hh : h ∈ Hsub (AF F) σ J P) (μ : Measure (Wsub (AF F) σ J P)),
      μ.IsAddHaarMeasure → μ.map (actW hh) = μ

end PI.VolSemiDirect.W.Md
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeUnipotentOfModulusOne
section
namespace PI.VolSemiDirect.W

theorem volume_unipotent_of_modulus_one (hM : Cj.ModOne) (hC : PiCont) (hR : PiRat) : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  volume_unipotent_of_adelic Lc.locally_compact_adelic_unitary discrete_adelic_unitary closed_subgroup_holds
    (semiStep_of Lc.locally_compact_adelic_unitary normal_subgroup_holds (projStep_of hC hR)) (Cj.conjStep_of hM)

end PI.VolSemiDirect.W
end

