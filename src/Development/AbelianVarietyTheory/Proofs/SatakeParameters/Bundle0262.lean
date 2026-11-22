import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.Columns.Bundle0054
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.Bundle0057
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0160
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.LocalToGlobal.Columns.Bundle0063
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong.LevAway

open Matrix GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.SplitPts GroundTheory.Automorphic GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem integral_iff (x : UA E a) :
    GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a ↔
      ∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem exists_compact_integral : ∃ C : Set (UA E a), IsCompact C ∧
    ∀ x ∈ finU E a, (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u a) → x ∈ C := by
  let Kf : Subgroup (finU E a) := (AdelicGLn.integralFiniteGL E a).comap (finPart E a)
  have hO : IsOpen (Kf : Set (finU E a)) := (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  have hc : IsCompact (Kf : Set (finU E a)) := by
    refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
    have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  refine ⟨Subtype.val '' (Kf : Set (finU E a)), hc.image continuous_subtype_val, fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (integral_iff x).2 hi

theorem exists_loc (w : HeightOneSpectrum (𝓞 E)) : ∃ f : UA E a → UA E a, Continuous f ∧
    ∀ x, f x ∈ locU a w ∧ cLoc w (f x) = cLoc w x := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
    refine ⟨fun x => (e.symm (cLoc w x)).1, continuous_subtype_val.comp (e.symm.continuous.comp (continuous_cLoc w)),
      fun x => ⟨(e.symm _).2, ?_⟩⟩
    rw [← he]; exact e.apply_symm_apply _
  · have hc : conjSrc (conjE E) w = w := conjSrc_eq_of_not_split hw
    have key : ∀ x : UA E a, finGL E a (locGL E a w (cLoc w x)) ∈ UA E a := by
      intro x
      refine finGL_mem_UA _ fun u => ?_
      by_cases hu : u = w
      · subst hu
        have e1 : ∀ v, v = u → GeneralLinearGroup.map (pLoc E v) (locGL E a u (cLoc u x)) = cLoc v x := by
          rintro v rfl; exact pLoc_locGL _ _
        rw [e1 _ hc, e1 u rfl]
        exact comp_eq x u
      · have h3 : conjSrc (conjE E) u ≠ w := fun e => hu (by rw [← conjSrc_conjSrc_cm u, e, hc])
        rw [pLoc_locGL_of_ne hu, pLoc_locGL_of_ne h3]
        simp
    refine ⟨fun x => ⟨finGL E a (locGL E a w (cLoc w x)), key x⟩, ?_, fun x => ⟨?_, ?_⟩⟩
    · exact Continuous.subtype_mk (continuous_finGL_ad.comp ((CuspSub.continuous_locGL w).comp (continuous_cLoc w))) _
    · refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
        Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
      rw [cLoc_finGL]
      exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
    · rw [cLoc_finGL]; exact pLoc_locGL _ _

theorem isClosed_finU : IsClosed ((finU E a : Subgroup (UA E a)) : Set (UA E a)) := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous (cInf (E := E) (n := a)) :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
  exact isClosed_eq hc continuous_const

theorem t2GL (w : HeightOneSpectrum (𝓞 E)) : T2Space (GL (Fin a) (w.adicCompletion E)) :=
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_levelOf (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a))
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) : IsClosed (levelOf a w₀ H : Set (UA E a)) := by
  have e : (levelOf a w₀ H : Set (UA E a)) = (finU E a : Set (UA E a)) ∩
      ((⋂ u, ⋂ (_ : ¬ Apart u w₀), {x | cLoc u x = 1}) ∩
        ⋂ w, ⋂ (_ : Apart w w₀), cLoc w ⁻¹' (cLoc w '' (H w : Set (UA E a)))) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_image]
  rw [e]
  refine isClosed_finU.inter (IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun w => isClosed_iInter fun _ => ?_))
  · haveI := t2GL (E := E) (a := a) u
    exact isClosed_eq (continuous_cLoc u) continuous_const
  · haveI := t2GL (E := E) (a := a) w
    exact ((hc w).image (continuous_cLoc w)).isClosed.preimage (continuous_cLoc w)

theorem exists_compact_of_finset (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) (hle : ∀ w, H w ≤ locU a w)
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ C : Set (UA E a), IsCompact C ∧ ∀ x ∈ finU E a, (∀ u, (∀ r ∈ R, Apart u r) → cLoc u x ∈ GlobalTheory.LFun.KGL u a) →
      (∀ r ∈ R, ∃ y ∈ H r, cLoc r y = cLoc r x) → x ∈ C := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hsub⟩ := exists_compact_integral (E := E) (a := a)
    exact ⟨C, hC, fun x hx hi _ => hsub x hx fun u => hi u (by simp)⟩
  | insert r R hr ih =>
    obtain ⟨C, hC, hsub⟩ := ih
    refine ⟨C * (H r : Set (UA E a)), hC.mul (hc r), fun x hx hi hH => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hH r (Finset.mem_insert_self r R)
    by_cases hap : ∀ r' ∈ R, Apart r' r
    · have hyl := hle r hy
      have hy1 : ∀ u, Apart u r → cLoc u y = 1 := fun u hu => ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2 u hu
      have hyf : y ∈ finU E a := (Subgroup.mem_inf.1 hyl).1
      refine ⟨x * y⁻¹, hsub _ (mul_mem hx (inv_mem hyf)) ?_ ?_, y, hy, inv_mul_cancel_right x y⟩
      · intro u hu
        by_cases hur : Apart u r
        · rw [map_mul, map_inv, hy1 u hur, inv_one, mul_one]
          refine hi u fun r' hr' => ?_
          rcases Finset.mem_insert.1 hr' with rfl | h
          · exact hur
          · exact hu r' h
        · have hz : cLoc r (x * y⁻¹) ∈ GlobalTheory.LFun.KGL r a := by
            rw [map_mul, map_inv, hyx, mul_inv_cancel]; exact one_mem _
          rcases eq_or_eq_conjSrc (not_not.1 hur) with rfl | rfl
          · exact hz
          · exact integral_conjSrc _ r hz
      · intro r' h
        obtain ⟨y', hy', e'⟩ := hH r' (Finset.mem_insert_of_mem h)
        exact ⟨y', hy', by rw [map_mul, map_inv, hy1 r' (hap r' h), inv_one, mul_one]; exact e'⟩
    · push_neg at hap
      obtain ⟨r', hr', hnr⟩ := hap
      have hxC : x ∈ C := by
        refine hsub x hx (fun u hu => hi u fun r'' hr'' => ?_) (fun r'' h => hH r'' (Finset.mem_insert_of_mem h))
        rcases Finset.mem_insert.1 hr'' with rfl | h
        · intro hh
          exact not_apart_trans (not_not.2 hh) (not_apart_symm hnr) (hu r' hr')
        · exact hu r'' h
      exact ⟨x, hxC, 1, one_mem _, mul_one x⟩

theorem isLevelAway_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  intro E _ _ _ a w₀ H hle _ hc ho hcof
  have hT := Filter.eventually_cofinite.1 hcof
  refine ⟨levelOf_le_finU w₀ H, fun x hx => (mem_levelOf.1 hx).2.1, ?_, ?_⟩
  · obtain ⟨C, hC, hsub⟩ := exists_compact_of_finset H hle hc hT.toFinset
    refine hC.of_isClosed_subset (isClosed_levelOf w₀ H hc) fun x hx => ?_
    obtain ⟨hf, h1, hw⟩ := mem_levelOf.1 hx
    refine hsub x hf (fun u hu => ?_) (fun r _ => ?_)
    · have hHu : H u = intU a u := by
        by_contra h
        exact hu u (hT.mem_toFinset.2 h) rfl
      by_cases h0 : Apart u w₀
      · obtain ⟨y, hy, e⟩ := hw u h0
        rw [hHu] at hy
        rw [← e]
        exact (mem_intU.1 hy).2 u (fun h => h rfl)
      · rw [h1 u h0]; exact one_mem _
    · by_cases h0 : Apart r w₀
      · exact hw r h0
      · exact ⟨1, one_mem _, by rw [map_one, h1 r h0]⟩
  · choose f hfc hf using fun w => exists_loc (E := E) (a := a) w
    let g : ∀ w, UA E a → locU a w := fun w x => ⟨f w x, (hf w x).1⟩
    have hg : ∀ w, Continuous (g w) := fun w => (hfc w).subtype_mk _
    have hpf : Continuous fun x : UA E a => GeneralLinearGroup.map (pFin E) (x : GA E a) :=
      (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
        continuous_subtype_val
    refine ⟨{x | GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a} ∩
      ⋂ w ∈ hT.toFinset, g w ⁻¹' ((H w).subgroupOf (locU a w) : Set (locU a w)), ?_, ?_, ?_⟩
    · exact ((AdelicGLn.isOpen_integralFiniteGL E a).preimage hpf).inter
        (isOpen_biInter_finset fun w _ => (ho w).preimage (hg w))
    · refine ⟨(integral_iff 1).2 fun u => by rw [map_one]; exact one_mem _, Set.mem_iInter₂.2 fun w _ => ?_⟩
      have h1 : f w 1 = 1 := eq_one_of_cLoc_eq_one (hf w 1).1 (by rw [(hf w 1).2, map_one])
      show (g w 1).1 ∈ H w
      show f w 1 ∈ H w
      rw [h1]; exact one_mem _
    · intro x hxN hxf hx1
      obtain ⟨hxi, hxH⟩ := hxN
      have hxi' := (integral_iff x).1 hxi
      refine mem_levelOf.2 ⟨hxf, hx1, fun w _ => ⟨f w x, ?_, (hf w x).2⟩⟩
      by_cases hwT : H w = intU a w
      · rw [hwT]; exact mem_intU_of (hf w x).1 (by rw [(hf w x).2]; exact hxi' w)
      · exact Set.mem_iInter₂.1 hxH w (hT.mem_toFinset.2 hwT)

end GlobalTheory.Cong.LevAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem xiOver_eq_XiTopG {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl

theorem xiOver_eq_XiTop : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  intro X Pr R Ch sel S mu cst u n h p Y p'
  exact xiOver_eq_XiTopG Ch sel mu cst n h p Y p'

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceMStatement
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twTt_k1Depth_twice_m : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ} (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)) (hc' : κ'⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), R.m = m2 + 2 → cst.Ok → ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → 2 * cst.M ≤ cst.D w → 2 * cst.M ≤ twTopDepth R → ((qOf w.1 : X.E) ^ cst.M) • y₁ ∈ stdAt X.E (R.N (m2 + 1)) w.1 → rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) * topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y) y₁ = (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) * topDat Ch sel mu cst (m2 + 1) w y y₁ := by
  first | exact @GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | exact GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | (intros; apply GlobalTheory.lastStepDatumLaw_K1Depth_twiceM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.TopInt

open GlobalTheory.PhiRootVal (RootOrZero phiGS_root phiG_root phiQ_root)
open GlobalTheory.CplTwoInt (intOff_prod ftY_intOff smul_symm_mem repY_mem)

theorem phiTopG_root {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (sharp : Bool) (i j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTopG (R := R) Ch mu sharp i j n P x) := by
  unfold PhiTopG
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem xiTop_intOff (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (u) (μ)
    (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (Yb : Set (Sp t.X.E (D.R.N i)))
    (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)) (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1)))
    (hY : Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  have hok := t.idx_ok μ
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem topInt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  intro D L hT Gi Gl K Y cX ex t hTop u μ c c' _ x
  obtain ⟨-, -, pt, ix, yb, pT, -, hyb, -, -, hpin, -, -⟩ := hTop u μ
  rw [hpin.2 c c' x]
  exact xiTop_intOff D L hT Gi Gl K Y cX ex t u μ _ _ _ _ _ (hyb c)

end GlobalTheory.TopInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtensionStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  first | exact @GlobalTheory.AboveL.mem_weil_of_fix | exact GlobalTheory.AboveL.mem_weil_of_fix | (intros; apply GlobalTheory.AboveL.mem_weil_of_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dif_pos (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dif_pos (by omega), Loc.atN, dif_pos hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem levGTop_rPsymF_eq_twLt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok →
    levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  intro X Pr R Ch _ _ _
  funext w
  rw [levGTop_PsymF]
  show _ = colLevSym Ch R.m w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dif_neg (by omega), dif_neg (by omega)]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.ConjUnder.cPl_under | exact GlobalTheory.ConjUnder.cPl_under | (intros; apply GlobalTheory.ConjUnder.cPl_under <;> assumption)
end

