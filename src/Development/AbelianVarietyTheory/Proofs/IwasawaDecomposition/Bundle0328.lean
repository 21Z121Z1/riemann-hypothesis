import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.FvOff
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

set_option maxHeartbeats 1000000 in

theorem fT_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w.asIdeal)
    (y y' η κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hκ : κ ∈ S.U) (hη : bc (prV (E := E) w) η = 1)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = y * η * κ) (z' : Fin n → E)
    (hx : ((bc (prV (E := E) w) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.1 *ᵥ z') a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z' a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w hw ⟨_, hx'⟩ = S.fT w hw ⟨_, hx⟩ := by
  have hk : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = η * κ := by
    rw [mul_assoc, he]; group
  have hkw : bc (prV (E := E) w) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      bc (prV (E := E) w) κ := by
    rw [hk, map_mul, hη, one_mul]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec w y y' γ z'
  rw [hkw] at hm
  have hloc : bc (prV (E := E) w) κ ∈ S.Uloc w := ((S.U_eq κ).1 hκ).2 w
  rw [S.UlocAlt w hw] at hloc
  obtain ⟨hg, hf⟩ := (Subgroup.mem_inf.1 hloc).2
  rw [← hf ⟨_, hx'⟩]
  congr 1
  exact Subtype.ext hm

set_option maxHeartbeats 1000000 in

theorem fT_adStep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w w' : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w'.asIdeal) (hne : w' ≠ w)
    (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hA : Formalism.L2.Herm.AdStep σ J S.U y y' γ w) (z z' : Fin n → E) (hz : z = γ.1 *ᵥ z')
    (hx : ((bc (prV (E := E) w') y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w') y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z' a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w' hw ⟨_, hx'⟩ = S.fT w' hw ⟨_, hx⟩ := by
  obtain ⟨κ, hκ, η, -, hη, he⟩ := hA
  subst hz
  exact fT_move S w' hw y y' η κ γ hκ (hη _ hne) he z' hx hx'

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ld_loc_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi (cc c)) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  refine GlobalTheory.DualCompletion.dual_move D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi (cc c)) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) (bwB_clsCrd_lat D u i hi (cc c))
    ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ld_in {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi (cc c)) :
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (v.adicCompletion D.host.F) (z a)) ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
  (ld_loc_ch K v c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_off_cls {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi)
    (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) K.lev.U (K.y c).1 (K.y c').1 γ (A.eV v).1) (hv : v' ≠ v)
    (z : Ld D u i hi c) (z' : Ld D u i hi c') (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (P.pr v' c' z') = (D.fm u).fv i v' c (P.pr v' c z) := by
  have hw : (A.eV v').1 ≠ (A.eV v).1 := fun h => hv (A.eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c z.1 z.2
  have hx' := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c' z'.1 z'.2
  have e := fT_adStep K.lev (A.eV v).1 (A.eV v').1 (A.eV v').2 hw (K.y c).1 (K.y c').1 γ hA z.1 z'.1 hz hx hx'
  exact (hT v' c' z' hx').trans ((congrArg (fMe v') e).trans (hT v' c z hx).symm)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_off_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}
    {res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v}
    (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T res i hi (fun c => clsCrd D u i hi c))
    (eV : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTieG L eV K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (hβ : chOf c' = chOf c) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (K (chOf c)).lev.U ((K (chOf c)).y ⟨c, rfl⟩).1
      ((K (chOf c)).y ⟨c', hβ⟩).1 γ (eV v).1) (hv : v' ≠ v)
    (z : LdG D i hi (clsCrd D u i hi c)) (z' : LdG D i hi (clsCrd D u i hi c')) (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (L.pr v' c' z') = (D.fm u).fv i v' c (L.pr v' c z) := by
  have hw : (eV v').1 ≠ (eV v).1 := fun h => hv (eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c, rfl⟩ z.1 z.2
  have hx' := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c', hβ⟩ z'.1 z'.2
  have e := fT_adStep (K (chOf c)).lev (eV v).1 (eV v').1 (eV v').2 hw _ _ γ hA z.1 z'.1 hz hx hx'
  exact (hT v' (chOf c) ⟨c', hβ⟩ z' hx').trans ((congrArg (fMe (chOf c) v') e).trans (hT v' (chOf c) ⟨c, rfl⟩ z hx).symm)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_eq_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  intro B X I hI hP l Z H F hF hC u i hi v v' c c' γ hA hv z z' hz
  by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
  · exact fv_off_cls ((F u).lv i hi) ((F u).cls i hi h) ((F u).fMe i hi h) ((F u).fv i hi h) v v' c c' γ (hA.1 h) hv z z' hz
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
    obtain ⟨hβ, hA'⟩ := hA.2 h1 h2
    have e := fv_off_ch ((F u).lvC i h1 h2) (F u).atT.eV ((F u).ch i h1 h2) ((F u).fMeC i h1 h2) ((F u).fvC i h1 h2)
      v v' c c' hβ γ hA' hv z z' hz
    have e1 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c).1 z z rfl
    have e2 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c').1 z' z' rfl
    exact (congrArg _ e2).symm.trans (e.trans (congrArg _ e1))

end GlobalTheory.Mem.Col2.HAt.FvOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHilbertModelInjectiveContainsGoodFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHilbertModel_injective_contains_goodForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  first | exact @GlobalTheory.LiftHilbertModel.hilbert_model_lift | exact GlobalTheory.LiftHilbertModel.hilbert_model_lift | (intros; apply GlobalTheory.LiftHilbertModel.hilbert_model_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrankStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  first | exact @GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | exact GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | (intros; apply GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  first | exact @GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | exact GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | (intros; apply GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyAStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  first | exact @GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | exact GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | (intros; apply GlobalTheory.linearIndependent_completion_of_irreducible_minpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

def LocalCondMoveDecoratedLattice (u : B.Word) (n : ℕ) (s : GA B n) (h : GLG B.fields.E n (B.primes X).vGs) : Prop :=
  s ∈ Formalism.L2.Herm.UstdAf B.sp.cm n ∧ Formalism.L2.Herm.Carries s (stdLat B.fields.E n) (stdLat B.fields.E n) ∧
  (∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n →
    HasRes P.1 (adAt B.host.F P.1 ((s⁻¹ : GA B n).1 r j)) (if j = r then 1 else 0)) ∧
  ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((s⁻¹ : GA B n).1 r j)) ((h w).1 r j)

def LocCQ (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (n : ℕ) (s : GA B n) (θ : GLQ B.fields.E n Q) : Prop :=
  ∀ (P : Q) (r j : Fin n), adAt B.host.F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
    algebraMap B.host.E _ ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecompositionStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_differ_by_decomposition : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  first | exact @GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | exact GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | (intros; apply GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRationalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_absolute_value_rational : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 → ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.ExtValueGroup.log_w_rat | exact GlobalTheory.ExtValueGroup.log_w_rat | (intros; apply GlobalTheory.ExtValueGroup.log_w_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutiveStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_involutive : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  first | exact @GlobalTheory.longElt_invT_involution | exact GlobalTheory.longElt_invT_involution | (intros; apply GlobalTheory.longElt_invT_involution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorelStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_unipotent_borel : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧ superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  first | exact @GlobalTheory.UnipFlip.longElt_invT_conj_unipB | exact GlobalTheory.UnipFlip.longElt_invT_conj_unipB | (intros; apply GlobalTheory.UnipFlip.longElt_invT_conj_unipB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadicalStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_unipotent_radical : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  first | exact @GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | exact GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | (intros; apply GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeRestrictionInjectiveOnMultiplicityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_restriction_injective_on_multiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj | exact GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj | (intros; apply GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj <;> assumption)
end

