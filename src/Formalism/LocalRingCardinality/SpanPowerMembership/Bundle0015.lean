import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0014
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeI
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0009
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowG

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.EmbeddingBaseFieldMul
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Emb

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

set_option synthInstance.maxHeartbeats 400000 in
theorem embedding_baseField_mul (R : D7) (hR : ∀ x : R.what₂.LL, x ∈ R.LL0) (i : R.ntw.Tw) (x : R.LL0) (y z : R.ntw.O0 i)
    (h : R.ntw.emb0 i x * algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) z =
      algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) y) :
    embAt R hR i (x : R.what₂.LL) * algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) z)) =
      algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) y)) := by
  have h1 := congrArg (iotaOk R i 1) h
  rw [map_mul, iotaOk_alg, iotaOk_alg] at h1
  have h2 : toLL0 R hR (x : R.what₂.LL) = x := Subtype.ext rfl
  show iotaOk R i 1 (R.ntw.emb0 i (toLL0 R hR (x : R.what₂.LL))) * _ = _
  rw [h2]
  exact h1

set_option synthInstance.maxHeartbeats 400000 in

def embCOf : EmbC D C where
  twI := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose
  twI_l := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.1
  embW := fun w => embAt (recN D C I he) hLL0 (cover_at (recN D C I he) hLL0 C.cover w).choose
  embW_w := fun w x => embAt_w (recN D C I he) hLL0 w _ (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.2 x
  embedding_baseField_condition := fun w x y z _ h => embedding_baseField_mul (recN D C I he) hLL0 _ x y z h

end Emb

section Good

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h)) (ht : THyp H) (n : ℕ)

set_option synthInstance.maxHeartbeats 400000 in

def nzInL : NzIn C where
  eA i _ := eAlgL H Lb what₂ h C i
  eL g := ((qcL H Lb what₂ h g : ℚ) : ↥LL0)
  eA_def i b g := eAlgL_def H Lb what₂ h C i b g
  eA_idem i _ := eAlgL_idem H Lb what₂ h C i
  eA_central i _ x := eAlgL_central H Lb what₂ h C i x
  Psi i := haveI := C.charZeroK i; PsiU H (FractionRing (C.O i)) Lb what₂ h
  hPsi i _ V _ _ := by
    have := C.charZeroK i
    have e : scalAct (FractionRing (C.O i)) V (PsiU H (FractionRing (C.O i)) Lb what₂ h) =
        actGL H (FractionRing (C.O i)) Lb what₂ h V := by
      ext g x; rfl
    unfold eAlgL
    rw [e]
    exact lift_actGL H (FractionRing (C.O i)) Lb what₂ h V ht
  ix j := {_a : Fin n // 1 ≤ j ∧ j ≤ R.m}
  ix_out _ := fun ⟨a⟩ => a.2
  ixM _ := Fin n
  rM _ := Subtype.val

end Good

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowP
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem unipotentSpace_le_baseSubspace (μ) : S.Usp μ ≤ S.V0 μ := inf_le_left

theorem sub_projQ_mem (μ) {x : S.Amb μ} (hx : x ∈ S.V0 μ) : x - (S.Qsp μ).starProjection x ∈ S.Usp μ := by
  set u := (S.Usp μ).starProjection x with hu
  have huU : u ∈ S.Usp μ := Submodule.starProjection_apply_mem _ _
  have hq : x - u ∈ S.Qsp μ :=
    ⟨Submodule.sub_mem _ hx (unipotentSpace_le_baseSubspace S μ huU), Submodule.sub_starProjection_mem_orthogonal x⟩
  have hp : (S.Qsp μ).starProjection x = x - u := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq fun w hw => ?_
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal huU hw.2
  rw [hp, sub_sub_cancel]
  exact huU

theorem RRset_gen (μ) : S.RRset μ = S.iota μ '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ))) := by
  unfold RowSide.RRset RowSide.LamSet
  rw [Set.image_image]
  refine Set.image_congr fun x hx => ?_
  have h : S.iota μ (x - (S.Qsp μ).starProjection x) = 0 := (sub_projQ_mem S μ hx.2).2
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

variable {μ : D.what₂.Tup} (s : EE →ₗ[ℂ] S.Amb μ) (hs : ∀ y, S.iota μ (s y) = y)
  (hV : ∀ y, s y ∈ S.V0 μ) (hU : ∀ y, ∀ u ∈ S.Usp μ, inner ℂ u (s y) = 0)
  (hiso : ∀ y z, inner ℂ (s y) (s z) = inner ℂ y z)

include hs hV hU in

theorem mem_Qsp_iff (x : S.Amb μ) : x ∈ S.Qsp μ ↔ x = s (S.iota μ x) := by
  have hsQ : ∀ y, s y ∈ S.Qsp μ := fun y => ⟨hV y, (Submodule.mem_orthogonal _ _).mpr (hU y)⟩
  constructor
  · intro hx
    have h1 : x - s (S.iota μ x) ∈ S.Usp μ :=
      ⟨Submodule.sub_mem _ hx.1 (hV _),
        (show S.iota μ (x - s (S.iota μ x)) = 0 by rw [map_sub, hs, sub_self])⟩
    have h2 : x - s (S.iota μ x) ∈ (S.Usp μ)ᗮ := Submodule.sub_mem _ hx.2 (hsQ _).2
    have h3 := Submodule.inner_right_of_mem_orthogonal h1 h2
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)
  · intro hx
    rw [hx]; exact hsQ _

include hs hV hU in
theorem iotaQ_bij' : Function.Bijective (S.iotaQ μ) := by
  refine ⟨fun a b h => Subtype.ext ?_, fun y => ⟨⟨s y, (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])⟩, hs y⟩⟩
  rw [(mem_Qsp_iff S s hs hV hU _).mp a.2, (mem_Qsp_iff S s hs hV hU _).mp b.2]
  exact congrArg s h

include hs hV hU hiso in
theorem iotaQ_adj' : S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ) = LinearMap.id := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  have hz : s y ∈ S.Qsp μ := (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])
  set q := LinearMap.adjoint (S.iotaQ μ) x with hq
  have h1 : inner ℂ q (⟨s y, hz⟩ : S.Qsp μ) = inner ℂ x (S.iotaQ μ ⟨s y, hz⟩) :=
    LinearMap.adjoint_inner_left _ _ _
  have h2 : S.iotaQ μ ⟨s y, hz⟩ = y := hs y
  rw [h2] at h1
  show inner ℂ (S.iota μ (q : S.Amb μ)) y = inner ℂ x y
  rw [← h1, ← hiso, ← (mem_Qsp_iff S s hs hV hU _).mp q.2]
  rfl

end Gen

end Formalism.BasicNotions.Examples₂.NZ
end
end

