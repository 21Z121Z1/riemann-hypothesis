import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainTieAndV0Onto
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem chainTie_and_v0Onto :
    ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool)
      (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), (R.DcPt → M.ChainTie) ∧ (R.ReadingFormsSpanGoodSubspace → M.GoodPartHasComplexCoordinates) := by
  intro D Bs A X fc s R cr M
  refine ⟨fun h u x y => ?_, fun h => ?_⟩
  · rw [M.cφ_eq, M.cF_eq]
    exact (h u x y).symm
  · unfold Seam.GoodPartHasComplexCoordinates
    rw [← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, M.cF_eq y⟩

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEq
section
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_latS_of_nsmul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L M : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ z ∈ M, T • z ∈ L) (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) M) :
    T • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
  have key : ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
      T • x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
    intro x hx
    unfold latS at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨T • z, h z hz, ?_⟩
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  exact key w hw

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_dual_mem_loc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hLb : Submodule.IsLattice E S.Lb := ⟨Module.Finite.iff_fg.mp S.Lb_fin, S.Lb_span⟩

  have hT : ∀ x ∈ dualL (σ : E →+* E) J S.Lb, T • x ∈ S.Lb := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact S.Lb_dual x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hdual := GlobalTheory.T.unitary_completion_maps_dualLattices F E σ n J v L S.Lb y hJ hL hLb hy hyl
  have h1 : (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  have h2 := nsmul_latS_of_nsmul v T S.Lb (dualL (σ : E →+* E) J S.Lb) hT _ ((hdual _).mp h1)
  rw [← Matrix.mulVec_smul] at h2
  have h3 := (hyl _).mpr h2
  have h4 : (fun a => inclE (F := F) (v.adicCompletion F) ((T • z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) L := by
    convert h3 using 1
    funext a
    simp
  exact GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion F E v n L hL (T • z) h4

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_dual_mem_loc_adelic {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (y.1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hloc : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hyl x
  exact nsmul_dual_mem_loc S hJ v L hL _ (Formalism.UG.P.afsplit_bc_mem σ J v y.1 y.2) hloc z hz

end Core

theorem loc_sup_ker_smul {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k) (t : R)
    (hu : Unram res t) (M N : Submodule R V) (h : ∀ z ∈ N, t • z ∈ loc res M) :
    loc res (M ⊔ RingHom.ker res • N) = loc res M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res _ x).mp hx
    have hle : M ⊔ RingHom.ker res • N ≤ loc res M := by
      refine sup_le (le_loc res M) ?_
      rw [Submodule.smul_le]
      intro a ha z hz
      obtain ⟨s', b, hs', hsab⟩ := hu.2 a (RingHom.mem_ker.mp ha)
      apply loc_sat res M s' _ hs'
      rw [smul_smul, hsab, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ b (h z hz)
    exact loc_sat res M s x hs (hle hsx)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res M x).mp hx
    exact (mem_loc res _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem loc_lk_eq_loc_cls : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  intro D u A i hi K v c
  refine loc_sup_ker_smul (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (GlobalTheory.T.levelPrime_unramifiedUniformizer D u A v) _ _ ?_
  intro z hz
  obtain ⟨r, hr, hrz⟩ := nsmul_dual_mem_loc_adelic K.lev (bwB_gramN_det D i hi) (A.eV v).1
    (clsCrd D u i hi c) (bwB_clsCrd_lat D u i hi c) (K.y c) (K.y_lat c) z hz
  refine (mem_loc _ _ _).mpr ⟨algebraMap _ _ r, fun h0 => hr ((A.res_v v r).mpr h0), ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]

end GlobalTheory.LevelHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
section
noncomputable section

namespace GlobalTheory.LevelHecke.MovePair

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem pairOf_act {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M M' : Submodule R V)
    (pr : M →+ W) (pr' : M' →+ W') (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (g : V ≃ₗ[R] V) (a : k)
    (h1 : ∀ z ∈ M', ∃ s, res s ≠ 0 ∧ s • g z ∈ M)
    (h2 : ∀ z, g z ∈ M → ∃ s, res s ≠ 0 ∧ s • z ∈ M')
    (h3 : ∀ z (hz : z ∈ M') (hg : g z ∈ M), φ' (pr' ⟨z, hz⟩) = a * φ (pr ⟨g z, hg⟩)) :
    (pairOf res M' pr' φ').act g = (pairOf res M pr φ).dil a := by
  have key : ∀ z, z ∈ loc res M' ↔ g z ∈ loc res M := by
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      refine loc_sat res M s _ hs0 ?_
      rw [← map_smul]
      exact (mem_loc _ _ _).2 (h1 _ h)
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      rw [← map_smul] at h
      exact loc_sat res M' s _ hs0 ((mem_loc _ _ _).2 (h2 _ h))
  ext x
  · rw [Pr.mem_act]
    show g.symm x ∈ loc res M' ↔ x ∈ loc res M
    rw [key, g.apply_symm_apply]
  · obtain ⟨z, rfl⟩ := g.surjective x
    show φ' (locExt res M' pr' (g.symm (g z))) = a * φ (locExt res M pr (g z))
    rw [g.symm_apply_apply]
    by_cases hz : z ∈ loc res M'
    · have hz' := (key z).1 hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      obtain ⟨t, ht0, h'⟩ := (mem_loc _ _ _).1 hz'
      have e1 : (t * s) • z ∈ M' := by rw [mul_smul]; exact M'.smul_mem _ h
      have e2 : (t * s) • g z ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ h'
      have e3 : g ((t * s) • z) ∈ M := by rw [map_smul]; exact e2
      have hne : res (t * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero ht0 hs0
      have e4 := h3 _ e1 e3
      have e5 : (⟨g ((t * s) • z), e3⟩ : M) = ⟨(t * s) • g z, e2⟩ := Subtype.ext (map_smul _ _ _)
      rw [e5, locExt_spec res M' pr' hs' z hz _ e1, locExt_spec res M pr hs _ hz' _ e2, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul] at e4
      apply mul_left_cancel₀ hne
      rw [e4]; ring
    · rw [locExt_off _ _ _ _ hz, locExt_off _ _ _ _ (fun h => hz ((key z).2 h)), map_zero, map_zero, mul_zero]

theorem mov_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (z : Fin n → E) :
    (bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y')).1 *ᵥ
      (((bc (prV (E := E) v) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) =
    ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) := by
  have e : (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) =
      (γ.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [e, mulVec_mulVec, ← Units.val_mul, map_mul, mul_inv_cancel_right, map_mul, map_inv, Units.val_mul,
    ← mulVec_mulVec]
  rfl

theorem mulsF_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hM : MulsF S v hv a h) {k : Type} [Ring k] (φ : S.fM v hv ≃+ k)
    (x x' : Fin n → E ⊗[F] v.adicCompletion F) (e : h.1 *ᵥ x = x') :
    (x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) ↔
      x' ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) ∧
    ∀ hx hx', φ (S.fT v hv ⟨x, hx⟩) = (a : k) * φ (S.fT v hv ⟨x', hx'⟩) := by
  subst e
  obtain ⟨hg, hf⟩ := hM
  refine ⟨hg x, fun hx hx' => ?_⟩
  rw [← hf ⟨x, hx⟩, map_zsmul, zsmul_eq_mul]

section Tied

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

theorem ld_lattice (c : (D.mem u).C.cls i) : Submodule.IsLattice D.host.E (Ld D u i hi c) := by
  have hL := bwB_clsCrd_lat D u i hi c
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  exact ⟨LocB.fg_of_le_bnd hd hle, LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem ld_loc (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K v := by
  refine GlobalTheory.T.unitary_completion_maps_dualLattices D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi c) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) (bwB_clsCrd_lat D u i hi c)
    ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

end Tied

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem pc_act_of_mulsF : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  intro D u A i hi P K fMe hT v c c' γ a hM
  have hin : ∀ c (z : Fin (D.R.N i) → D.host.E), z ∈ Ld D u i hi c →
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 :=
    fun c z hz => (ld_loc K _ c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hout : ∀ c (z : Fin (D.R.N i) → D.host.E),
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 →
      ∃ s, A.res v s ≠ 0 ∧ s • z ∈ Ld D u i hi c := by
    intro c z hz
    obtain ⟨r, hr, h⟩ := GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion D.host.F D.host.E (A.eV v).1 _ _ (ld_lattice c) z ((ld_loc K _ c _).2 hz)
    exact ⟨_, fun h0 => hr ((A.res_v v r).2 h0), h⟩
  have hst := fun z => mulsF_apply K.lev _ _ a _ hM (fMe v) _ _
    (mov_mulVec (A.eV v).1 (K.y c).1 (K.y c').1 γ z)
  refine pairOf_act _ _ _ _ _ _ _ (P.pr_smul v c) (P.pr_smul v c') (glE γ) _
    (fun z hz => hout c (γ.1 *ᵥ z) ((hst z).1.1 (hin c' z hz)))
    (fun z hz => hout c' z ((hst z).1.2 (hin c (γ.1 *ᵥ z) hz))) (fun z hz hz' => ?_)
  · have hz2 : γ.1 *ᵥ z ∈ Ld D u i hi c := hz'
    have hT' : ∀ c (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c), (D.fm u).fv i v c (P.pr v c ⟨z, hz⟩) =
        fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hin c z hz⟩) := fun c z hz => hT v c ⟨z, hz⟩ (hin c z hz)
    have e1 := hT' c' z hz
    have e2 := hT' c _ hz2
    exact e1.trans (((hst z).2 _ _).trans (congrArg (fun t => (a : (D.mem u).A.Fv v) * t) e2.symm))

end GlobalTheory.LevelHecke.MovePair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEq
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeWittLoc

open Matrix Formalism.UG

theorem exists_quasiReflection {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin n → S) (c : S)
    (hc : c + s c = c * s c * hform s J w w) :
    ∃ g g' : Matrix (Fin n) (Fin n) S, g' * g = 1 ∧ cT s g * J = J * g' ∧
      ∀ z, g *ᵥ z = z - (c * hform s J w z) • w := by
  let r : Fin n → S := fun j => ∑ i, s (w i) * J i j
  have hr : ∀ z, r ⬝ᵥ z = hform s J w z := fun z => by
    simp only [r, dotProduct, hform, Finset.sum_mul]
    exact Finset.sum_comm
  let P : Matrix (Fin n) (Fin n) S := vecMulVec w r
  have hPP : P * P = hform s J w w • P := by
    ext i j
    rw [← hr]
    simp only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : cT s P * J = J * P := by
    ext i j
    have h1 : s (r i) = ∑ k, J i k * w k := by
      simp only [r, map_sum, map_mul, hs, hJ]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]
    calc ∑ k, s (w k) * s (r i) * J k j = s (r i) * r j := by
          simp only [r, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          rw [h1, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul,
      mul_comm (s c) c, ← hc, add_smul]
    abel
  · have : cT s (1 - c • P) = 1 - s c • cT s P := by
      ext i j
      simp [cT, Matrix.one_apply, eq_comm]
    rw [this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul,
      Matrix.mul_one]
  · rw [sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]
    congr 2
    funext i
    simp only [P, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_unitary {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → S) (β v : S)
    (hx : hform s J x x = β) (hy : hform s J y y = β) (hv : v * s v = 1)
    (hD : IsUnit (β - v * hform s J y x)) :
    ∃ γ : GL (Fin n) S, cT s γ.1 * J * γ.1 = J ∧ γ.1 *ᵥ x = y := by
  have hsym : ∀ a b, s (hform s J a b) = hform s J b a := fun a b => by
    simp only [hform, map_sum, map_mul, hs, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hD.exists_left_inv
  have hβ : s β = β := by rw [← hx, hsym]
  have hc' : s c * (β - s v * hform s J x y) = 1 := by
    have := congrArg s hc
    rwa [map_mul, map_sub, map_mul, hsym, hβ, map_one] at this
  obtain ⟨g, g', h1, h2, h3⟩ := exists_quasiReflection s hs J hJ (x - s v • y) c (by
    rw [hl, hrr, hrr, hx, hy]
    linear_combination (-c) * hc' - s c * hc - c * s c * β * hv)
  have h4 : g * g' = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hv, h4, one_smul]
  · rw [smul_mul_smul_comm, mul_comm, hv, h1, one_smul]
  · have : cT s (v • g) = s v • cT s g := by
      ext i j
      simp [cT]
    show cT s (v • g) * J * (v • g) = J
    rw [this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul,
      Matrix.mul_one]
  · show (v • g) *ᵥ x = y
    rw [smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]

theorem exists_isUnit_sub {S : Type} [CommRing S] [Finite (MaximalSpectrum S)] (v : ℕ → S)
    (hv : ∀ k l, k ≠ l → IsUnit (v k - v l)) (β t : S) (hβ : IsUnit β) :
    ∃ k, IsUnit (β - v k * t) := by
  by_contra h
  push Not at h
  choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)
  obtain ⟨k, l, hkl, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))
  have he' : m k = m l := congrArg MaximalSpectrum.asIdeal he
  have h1 := hmem l
  rw [← he'] at h1
  have h2 : (v k - v l) * t ∈ m k := by
    have := (m k).sub_mem h1 (hmem k)
    convert this using 1
    ring
  have h3 : t ∈ m k := ((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2
  have h4 : β ∈ m k := by
    have := (m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)
    rwa [sub_add_cancel] at this
  exact (hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)

theorem exists_normOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k, a k * σ (a k) = 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | (apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)

theorem exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy
  have := hR'.1
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  obtain ⟨a, ha, hn⟩ := exists_normOne hcm
  obtain ⟨k, hk⟩ := exists_isUnit_sub (fun k => inclR R (a k))
    (fun k l hkl => by
      rw [← map_sub]
      exact (IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)
    (algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)
  obtain ⟨γ, h1, h2⟩ := exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J)
    (fun i j => by
      show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
      rw [hJ.1])
    (x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))
    (by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by
      show inclR R (a k) * inclR R (σ (a k)) = 1
      rw [← map_mul, hn, map_one])
    hk
  refine ⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h2

end GlobalTheory.GaugeWittLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpenStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_stabilizer_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Af F) σ J h : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Af F) σ J)) ∧ IsCompact (K : Set (HA (Af F) σ J)) := by
  first | exact @GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | exact GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | (intros; apply GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePairStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryTwoStepVectorAndTranslatePair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E), Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  first | exact @GlobalTheory.GaugeEx.continuous_pairOf_joint | exact GlobalTheory.GaugeEx.continuous_pairOf_joint | (intros; apply GlobalTheory.GaugeEx.continuous_pairOf_joint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompactStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_hermitian_eq_pm_gram_unitary_compact : ∀ (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Formalism.UG.HasSignature J p q → (p = 0 ∨ q = 0) → (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧ IsCompact (Formalism.QuantumDeterminants.UH J) := by
  first | exact @GlobalTheory.DefiniteFrame.definite_frame | exact GlobalTheory.DefiniteFrame.definite_frame | (intros; apply GlobalTheory.DefiniteFrame.definite_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstantsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Γ : Type) [CommGroup Γ] (c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) → Matrix (Fin (M + 1)) (Fin M) E → Γ), (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E), 2 ≤ M → StepData σ J x a B J' → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → c M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)) x₂ B₂ = c M J x B) → (∀ (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → c (M + 1) J x₁ B₁ * c M J₁ y₁ C₁ = c (M + 1) J x₂ B₂ * c M J₂ y₂ C₂) → ∃ α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → Γ, (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J → α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) = α M J) ∧ ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x a B J' → α (M + 1) J = c M J x B * α M J' := by
  first | exact @GlobalTheory.GaugeAlg.exists_coboundary | exact GlobalTheory.GaugeAlg.exists_coboundary | (intros; apply GlobalTheory.GaugeAlg.exists_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normal_flat_closure : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  first | exact @GlobalTheory.GraphClosure.exists_normalisation_of_locallyClosed | exact GlobalTheory.GraphClosure.exists_normalisation_of_locallyClosed | (intros; apply GlobalTheory.GraphClosure.exists_normalisation_of_locallyClosed <;> assumption)
end

