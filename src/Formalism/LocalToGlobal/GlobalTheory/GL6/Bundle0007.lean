import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRUpLoc
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem bwL_descent (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E)
    (he : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.inclE (F := F) (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AF F) e ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.SS F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨D, hD, hDe⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  set d : E := algebraMap F E (D : F) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; intro h
    exact hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))
  have hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range := by
    intro k
    have := hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)
    rwa [Algebra.smul_def] at this
  let f : 𝓞 E →ₗ[ℤ] E := LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
  have hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    obtain ⟨y, hy⟩ := hpow k
    exact ⟨y, by simp [f, hy, hd0]⟩
  have : IsNoetherian ℤ (LinearMap.range f) := by
    exact isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have : IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule := isNoetherian_of_le hS
  have hint : IsIntegral ℤ e :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e
      (Algebra.subset_adjoin (Set.mem_singleton e))
  exact ⟨⟨e, hint⟩, rfl⟩

variable (D : D7) (u : D.what₂.Word)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bwL_lcInt (Tt : FormsTied D u) : BwLcInt D u := by
  intro i hi c x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat ((Tt.cls i hi).y c).1 (Tt.cls i hi).lev.Lb := by
    intro z hz
    exact ((Tt.cls i hi).y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ (Tt.cls i hi).lev.Lb, ∀ b ∈ (Tt.cls i hi).lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := (Tt.cls i hi).lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) (Tt.cls i hi).lev.Lb 1 hm ((Tt.cls i hi).y c).1
    ((Tt.cls i hi).y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

variable (D : D7) (u : D.what₂.Word)

private theorem isLattice_map_restrictScalars_linearEquiv {K R V W : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (e : V ≃ₗ[K] W) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (L.map ((e : V →ₗ[K] W).restrictScalars R)) := by
  obtain ⟨hfg, hsp⟩ := hL
  refine ⟨hfg.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top,
    LinearEquiv.range]

theorem bwB_clsCrd_lat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule.IsLattice D.host.E (clsCrd D u i hi c) := by
  have hL : Submodule.IsLattice D.host.E (D.clsLat u i c) := by
    first
      | exact D.clsLat_lat u i c
      | exact D.clsLat_isLat u i c
      | exact D.clsLat_isLattice u i c
      | exact D.clsLat_lattice u i c
      | exact (D.clsLat_spec u i c).1
      | exact D.clsLat_spec u i c
      | exact inferInstance
  unfold clsCrd
  exact isLattice_map_restrictScalars_linearEquiv _ _ hL

theorem bwB_gramN_det (i : ℕ) (hi : i ≤ D.R.m) : IsUnit (gramN D i hi).det := by
  letI := D.host.cmStar
  unfold gramN
  rw [Matrix.det_reindex_self, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfa : ∀ a, (D.sp.X i).hT ((D.sp.X i).frame a) (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro a
    have h := congrFun hv a
    have e : Matrix.mulVec (D.sp.X i).gram v a =
        ∑ b, (D.sp.X i).hT ((D.sp.X i).frame a) ((D.sp.X i).frame b) * v b := rfl
    rw [e] at h
    simp only [map_sum, map_smul, smul_eq_mul]
    simpa [mul_comm] using h
  have hy : ∀ x, (D.sp.X i).hT x (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro x
    have h0 : (D.sp.X i).hT.flip (∑ b, v b • (D.sp.X i).frame b) = 0 :=
      (D.sp.X i).frame.ext (fun a => by simpa using hfa a)
    simpa using congrArg (fun f => f x) h0
  have hy0 := (D.sp.X i).nondeg.2 _ hy
  have hz := Fintype.linearIndependent_iff.mp (D.sp.X i).frame.linearIndependent v hy0
  exact hv0 (funext hz)

theorem local_bases_exist_of_compatible_forms (Tt : FormsTied D u) : BwLocBases D u Tt := by
  haveI : Fact (Nat.Prime (D.mem u).A.T) := ⟨(D.mem u).A.T_prime⟩
  intro i hi c
  have hL : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  obtain ⟨_, hspL⟩ := id hL
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (bwB_gramN_det D i hi) _ hL
  obtain ⟨d1, hd1, hle1⟩ := LocB.exists_le_bnd _ hL
  have hsp : Submodule.span D.host.E ((Ld D u i hi c : Submodule _ _) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ :=
    LocB.dual_span _ _ _ hL
  have hfg : (Ld D u i hi c).FG := by
    clear hle1 hd1 hsp hspL
    have h0 := LocB.fg_of_le_bnd hd hle
    unfold Ld dualL at *
    convert h0 using 3
  refine ⟨LocB.exists_isLocBasis (D.mem u).A.T _ (Ld D u i hi c) hfg hsp, fun v => ?_⟩
  have hle2 : Lk Tt.atT i hi v c ≤ LocB.bnd (d1 * d) := by
    refine sup_le (hle1.trans ?_) (Submodule.smul_le_right.trans (hle.trans (LocB.bnd_mono d d1)))
    rw [mul_comm]
    exact LocB.bnd_mono d1 d
  have hspK : Submodule.span D.host.E ((Lk Tt.atT i hi v c : Submodule _ _) :
      Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← hspL]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have hfgK : (Lk Tt.atT i hi v c).FG := LocB.fg_of_le_bnd (mul_ne_zero hd1 hd) hle2
  exact LocB.exists_isLocBasis (D.mem u).A.T _ (Lk Tt.atT i hi v c) hfgK hspK

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PUpNat
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem upn_isTr_inv (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (s : (D.mem u).C.Y i) :
    IsTr (atInf (embT D) γ.1.1)
      ((Tf.val i hi).eY ((Tf.val i hi).eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).inv_mem γ.2) ((Tf.val i hi).eY s))))
      ((Tf.val i hi).eY s) := by
  intro τ
  rw [Equiv.apply_symm_apply]
  show ((Tf.val i hi).eY s).1 τ = atInf (embT D) (γ.1 : Matrix _ _ D.host.E) τ *
    (atInf (embT D) ((γ.1⁻¹ : GL _ D.host.E) : Matrix _ _ D.host.E) τ * ((Tf.val i hi).eY s).1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem upNat_of_tied (Tf : FormsTied D u) : UpNat Tf := by
  intro i hi v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := Tf.upN i hi v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun h => ?_⟩
  funext s
  rw [h6 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl

set_option maxHeartbeats 4000000 in

theorem dnNat_of_tied (Tf : FormsTied D u) : DnNat Tf := by
  intro i hi v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := Tf.dnN i hi v c g hg0
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun h => ?_⟩
  funext s
  rw [h5 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl

theorem rnd_roundUp_ofM (Tf : FormsTied D u) (hL : RUpLocM Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u :=
  rnd_roundUpN Tf (upNat_of_tied Tf) (dnNat_of_tied Tf) hL

theorem rnd_roundDn_ofM (Tf : FormsTied D u) (hL : RDnLocM Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u :=
  rnd_roundDnN Tf (upNat_of_tied Tf) (dnNat_of_tied Tf) hL

theorem rnd_linkAdmT_ofM
    (h : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → RUpLocM Tf ∧ RDnLocM Tf) :
    LinkAdmT :=
  rnd_linkAdmT_ofN fun D u Tf hc =>
    ⟨upNat_of_tied Tf, dnNat_of_tied Tf, (h D u Tf hc).1, (h D u Tf hc).2, splitAtT_of_tied Tf.atT⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

