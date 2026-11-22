import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClassesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTrans
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalTrans

open Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem isScalar_trans {Λ : Submodule (𝓞 E) S.V} {r k : ℕ} {T T' : E} {F : LFlag S r T}
    {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}
    (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (hz : β F'.fl.z = F''.fl.z)
    (hs1 : s0 Λ F F' F'' β k = 1) (hS1 : IsScalar Λ F F' F'' β) (hS2 : IsScalar Λ F F'' F''' γ) :
    IsScalar Λ F F' F''' (β.trans γ) := by
  have n' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL' hG'
  have n'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL'' hG''
  have hTh1'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hΛ hdim n' n'' hs1
  intro y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'
  have hy1b : y1 ∈ orth S (Xplus F) := hy1.2
  have hy1'b : y1' ∈ orth S (Xplus F') := hy1'.2
  have hy2 : y1 ∈ Ylift Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh1'' hy1, hy1b⟩
  have hy2' : β y1' ∈ Ylift' Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi hX hTh1'' hy1',
      _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.mapOrthXplusQ hi hX hz hy1'b⟩
  have a := hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'
  have b := hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'
  exact a.trans b

end Gen

theorem scalar_pair_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 →
    (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 →
    (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  intro D X Y u u' t t' t'' hG hG' hG'' h1 hsc1 h2 hsc2
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ s : TauC Y u u', s.G ≠ 0 → Gval (lf D (X.Fu u)) s.frame ≠ 0 := fun s hs h =>
    hs ((Formalism.L2.SG.Pf.SatGram.gterm_G Y s).trans h)
  have hlat : Submodule.IsLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ s : TauC Y u u', IsLift s.lam s.frame := fun s => s.rep.2.2.2.2.1
  obtain ⟨⟨hl1, hl1'⟩, hs1, hS1⟩ := (show scalT t t' from hsc1)
  obtain ⟨⟨hl2, hl2'⟩, hs2, hS2⟩ := (show scalT t' t'' from hsc2)
  rw [← hl1] at hs2 hS2
  have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
  have hL'' : IsLift t.lam t''.frame := by rw [hl1, hl2]; exact hLt t''
  have hth1 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF (hLt t)
    (hGv t hG)).1 hs1
  have hth2 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t'.frame t''.frame _ hLF hL'
    (hGv t' hG')).1 hs2
  have htr := Formalism.L2.SG.NGCut.CorankRelation.Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹)
    (t''.lin * t'.lin⁻¹) (fun x hx => (Formalism.L2.SG.NGCut.CorankRelation.frame_mem_iff t' t'' x).1 hx) hth1 hth2
  have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
  rw [hmul] at htr
  have hs3 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t''.frame (t''.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t''.frame _ hLF (hLt t) (hGv t hG)).2 htr

  have hi1 := t.rep.2.2.1
  have hi2 := t'.rep.2.2.1
  have hiβ : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi2 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi1)
  have hX : ∀ j, (Xflag t.frame j).map ((t'.lin * t.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
      (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag t'.frame j := by
    intro j
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t'.lin hi2,
      ← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hz : (t'.lin * t.lin⁻¹) t.frame.fl.z = t'.frame.fl.z := by
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t'.lin hi2]
    simp
  have hsc3 := isScalar_trans (β := t'.lin * t.lin⁻¹) (γ := t''.lin * t'.lin⁻¹) hlat hdim hLF (hLt t) (hGv t hG) hL'
    (hGv t' hG') hiβ hX hz hs1 hS1 hS2
  have e3 : (t'.lin * t.lin⁻¹).trans (t''.lin * t'.lin⁻¹) = t''.lin * t.lin⁻¹ := hmul
  rw [e3] at hsc3
  have hl : t.lam = t''.lam ∧ t.lam' = t''.lam' := ⟨hl1.trans hl2, hl1'.trans hl2'⟩
  refine ⟨?_, ?_⟩
  · show s0T t t'' = 1
    unfold s0T
    rw [if_pos hl]
    exact hs3
  · show scalT t t''
    exact ⟨hl, hs3, hsc3⟩

end GlobalTheory.ScalTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTrivialTranslateLocalComponentDisjointOrLe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SlocDich.translate_dichotomy : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  intro L _ _ _ n s τ i T _hTi hT y hy P hP
  have hpart := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s

  have hstab : ∀ (g : GL (Fin n) (s.w.adicCompletion L)) (a : τ.V),
      a ∈ P.comap ((NG.rt L n y).comp T) → τ.ρ g a ∈ P.comap ((NG.rt L n y).comp T) := by
    intro g a ha
    obtain ⟨x, ⟨hx, hxA⟩, -⟩ := hpart.2.2 (Matrix.GeneralLinearGroup.map i.symm.toRingHom g)
    have hg : g = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) := by
      rw [hxA]; ext j k; simp
    have hc := hpart.2.1 x y hx hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply] at ha ⊢
    rw [hg, hT x hx a]
    have e : NG.rt L n y (NG.rt L n x (T a)) = NG.rt L n x (NG.rt L n y (T a)) := by
      funext g'
      show T a (g' * y * x) = T a (g' * x * y)
      rw [mul_assoc, mul_assoc, hc.eq]
    rw [e]
    exact hP x hx _ ha
  let Q : Subrepresentation τ.ρ := ⟨P.comap ((NG.rt L n y).comp T), hstab⟩
  rcases τ.irr.eq_bot_or_eq_top Q with h | h
  · left
    rw [Submodule.disjoint_def]
    rintro f ⟨a, rfl⟩ hf
    have ha : a ∈ Q.toSubmodule := hf
    rw [h] at ha
    have : a = 0 := ha
    simp [this]
  · right
    rintro f ⟨a, rfl⟩
    have ha : a ∈ Q.toSubmodule := by rw [h]; trivial
    exact ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_le_encard_fibres {α Θ : Type} (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ)
    (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ) (hf : ∀ a ∈ S, 0 ≤ f a)
    (hR : ∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a))
    (hB : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) :
    ENNReal.ofReal (∑ a ∈ S, f a) ≤
      ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) :=
  GlobalTheory.T.sum_fibre_two_index_encard_bound α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB

theorem sum_pairs_le_classes (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W))
    (hh : ∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) (Sf : Finset (GTu Y u × GTu Y u))
    (hSf : ∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ)
    (hη : ∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) :
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
  GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses D large₂ X Y u hS W HW he Λ h hh Sf hSf hη

theorem sum_classes_le (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E)
    (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS)
    (A : Finset (GTu Y u)) (hne : A.Nonempty)
    (hA : ∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧
      (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) :
    ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x :=
  GlobalTheory.T.sum_frameClassWeights_le_datumBound D large₂ X Y u hS W HW he Λ j x δ d N A hne hA

theorem termData (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (t : GTu Y u) (ht : t ∈ relSet Y u) :
    ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
  obtain ⟨N, hA, hj, hT⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS t ht
  have hterm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hS t N hA
  obtain ⟨-, -, hDel, hDb, hlab⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hS t N hA
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨-, hx1, hxD, -, hdim⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t)
    (dI D) N (gS D) t.lam hg he hA hterm
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS N (gS D) t.lam hg hterm
  have hiso : t.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => t.rep.2.2.1 x y
  obtain ⟨h, hh, hH, -, -⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t) (dI D) N
    t.lin he hA hiso (fun a => GlobalTheory.TypeAsm.FibProof.Ft_e t a)
  exact ⟨N, h, hA, hterm, hj, hT, hDel, hDb, hDel1, hDb1, hx1, hxD, hlab, hh, hH, by omega⟩

theorem pairTrip (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (p : GTu Y u × GTu Y u) (hp : p ∈ (Y.tO u u).allPairs (relSet Y u))
    (N₁ N₂ : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h₁ h₂ : W ≃ₗ[D.host.E] W) (hA₁ : AdT p.1 N₁) (hA₂ : AdT p.2 N₂)
    (ht₁ : N₁.IsTerm (gS D) p.1.lam) (ht₂ : N₂.IsTerm (gS D) p.2.lam)
    (hH₁ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.1) W.subtype p.1.lin h₁)
    (hH₂ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.2) W.subtype p.2.lin h₂) :
    p.1.lam = p.2.lam ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) p.1.lam,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) p.1.lam, h₁ * h₂⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype p.1.lam) D.R.rS (N₁.gI (gS D) p.1.lam)
          (N₂.gI (gS D) p.1.lam) := by
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨hl, hl', hc⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, hp.2.2⟩
  refine ⟨hl, ?_⟩
  have hi₁ : p.1.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.1.rep.2.2.1 x y
  have hi₂ : p.2.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.2.rep.2.2.1 x y
  have hΛ₁ : p.1.lin • p.1.lam' = p.1.lam := by
    rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.1.rep.2.2.2.1
  have hΛ₂ : p.2.lin • p.1.lam' = p.1.lam := by
    rw [hl, hl', ← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.2.rep.2.2.2.1
  rw [← hl] at ht₂
  exact GlobalTheory.DegAsm.trip_of_terms D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft p.1) (Ft p.2) (dI D)
    N₁ N₂ (gS D) p.1.lam p.1.lam' p.1.lin p.2.lin h₁ h₂ hg he hA₁ hA₂ ht₁ ht₂ hi₁ hi₂
    (fun a => ⟨GlobalTheory.TypeAsm.FibProof.Ft_e p.1 a, GlobalTheory.TypeAsm.FibProof.Ft_e p.2 a⟩) hΛ₁ hΛ₂ hH₁ hH₂ hc

end GlobalTheory.TypeAsm.PerRow

namespace GlobalTheory.TypeAsm
open PerRow

theorem perRowC : PerRowC := by
  intro D large₂ X Y u hS W HW he Λ j' j'' δ' δ'' S hS'
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N₀, h₀, -⟩ := termData D large₂ X Y u hS W HW he p₀.1 (hS' p₀ hp₀).1.1
  have hdata : ∀ t : GTu Y u, ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), t ∈ relSet Y u →
      AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
    intro t
    by_cases ht : t ∈ relSet Y u
    · obtain ⟨N, h, hp⟩ := termData D large₂ X Y u hS W HW he t ht
      exact ⟨N, h, fun _ => hp⟩
    · exact ⟨N₀, h₀, fun h => absurd h ht⟩
  choose N h hNh using hdata

  have hpair : ∀ p ∈ S, p.2.lam = Λ ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS ((N p.1).gI (gS D) Λ)
          ((N p.2).gI (gS D) Λ) ∧
      (N p.1).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊ ∧ (N p.2).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊ := by
    intro p hp
    obtain ⟨hpa, hl, hj1, hj2, hd1, hd2⟩ := hS' p hp
    obtain ⟨a1, a2, -, -, a5, -, -, -, a9, a10, -, -, a13, -⟩ := hNh p.1 hpa.1
    obtain ⟨b1, b2, -, -, b5, -, -, -, b9, b10, -, -, b13, -⟩ := hNh p.2 hpa.2.1
    obtain ⟨hl2, htr⟩ := pairTrip D large₂ X Y u hS W HW he p hpa (N p.1) (N p.2) (h p.1) (h p.2) a1 b1 a2 b2 a13 b13
    rw [hl] at htr hl2 a9 a10
    rw [← hl2] at b9 b10
    refine ⟨hl2.symm, htr, Finset.mem_Icc.2 ⟨a9, Nat.le_floor ?_⟩, Finset.mem_Icc.2 ⟨b9, Nat.le_floor ?_⟩⟩
    · rw [← hj1, ← hd1, ← a5]; exact a10
    · rw [← hj2, ← hd2, ← b5]; exact b10
  refine sum_le_encard_fibres S (fun p => (N p.1).gI (gS D) Λ) (fun p => (N p.2).gI (gS D) Λ)
    (fun p => (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹))
    (fun x y => GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x y)
    (fun p => wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2))
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x)
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x) _ _ ?_
    (fun p hp => ⟨(hpair p hp).2.2.1, (hpair p hp).2.2.2, (hpair p hp).2.1⟩) ?_
  · intro p _
    have hw : 0 ≤ wRow D (X.Fu u) p.1.lam' := by unfold wRow; positivity
    have ho : ∀ t : GTu Y u, 0 ≤ omT t := fun t =>
      ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
    exact mul_nonneg hw (mul_nonneg (ho _) (ho _))
  · intro a ha
    have key : ∀ Sf : Finset (GTu Y u × GTu Y u), (∀ q ∈ Sf, q ∈ S ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.1) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ ∧
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.2) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ ∧ h q.1 * (h q.2)⁻¹ = h a.1 * (h a.2)⁻¹ ∧
        (N q.1).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧ (N q.2).gI (gS D) Λ = (N a.2).gI (gS D) Λ) → a ∈ Sf →
        ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) ((N a.1).gI (gS D) Λ) *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) ((N a.2).gI (gS D) Λ) := by
      intro Sf hmem haf
      have h1 := sum_pairs_le_classes D large₂ X Y u hS W HW he Λ h (fun t ht => (hNh t ht).2.2.2.2.2.2.2.2.2.2.2.2.1) Sf
        (fun p hp => ⟨(hS' p (hmem p hp).1).1, (hS' p (hmem p hp).1).2.1⟩)
        (fun p hp q hq => ((hmem p hp).2.2.2.1).trans ((hmem q hq).2.2.2.1).symm)
      have hA1 : ∀ t ∈ Sf.image Prod.fst, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j' ∧ labT t = δ' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, c1, -, -, c4, -⟩ := hmem q hq
        obtain ⟨hpa, hl, hj1, -, hd1, -⟩ := hS' q hqS
        obtain ⟨a1, a2, -⟩ := hNh q.1 hpa.1
        rw [hl] at a2
        exact ⟨hpa.1, hl, hj1, hd1, a1, a2, c4, c1⟩
      have hA2 : ∀ t ∈ Sf.image Prod.snd, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j'' ∧ labT t = δ'' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.2).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, -, c2, -, -, c5⟩ := hmem q hq
        obtain ⟨hpa, -, -, hj2, -, hd2⟩ := hS' q hqS
        have hl2 := (hpair q hqS).1
        obtain ⟨b1, b2, -⟩ := hNh q.2 hpa.2.1
        rw [hl2] at b2
        exact ⟨hpa.2.1, hl2, hj2, hd2, b1, b2, c5, c2⟩
      have h2 := sum_classes_le D large₂ X Y u hS W HW he Λ j' _ δ' _ N (Sf.image Prod.fst) ⟨a.1, Finset.mem_image_of_mem _ haf⟩ hA1
      have h3 := sum_classes_le D large₂ X Y u hS W HW he Λ j'' _ δ'' _ N (Sf.image Prod.snd) ⟨a.2, Finset.mem_image_of_mem _ haf⟩ hA2
      rw [Finset.image_image] at h2 h3
      have n2 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      have n1 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      exact h1.trans (mul_le_mul h2 h3 n2 (n1.trans h2))

    rw [Finset.filter_congr_decidable]
    refine key _ (fun q hq => ?_) (Finset.mem_filter.2 ⟨ha, rfl, rfl, rfl⟩)
    obtain ⟨hqS, he1, he2, he3⟩ := Finset.mem_filter.1 hq
    obtain ⟨c1, c2⟩ := Prod.mk.inj he1
    obtain ⟨c2, c3⟩ := Prod.mk.inj c2
    exact ⟨hqS, c1, c2, c3, he2, he3⟩

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SlocVal

theorem tendsto_pow_map {A B : Type} [Ring A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {x : A} (hx : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem continuous_symm {A B : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    [SigmaCompactSpace A] [Field B] [TopologicalSpace B] [IsTopologicalRing B] [BaireSpace B]
    [T2Space B] (e : A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective he
  exact e.toEquiv.continuous_symm_iff.2 ho

end GlobalTheory.SlocVal

open GlobalTheory.SlocVal in

theorem GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  intro L _ _ _ s g _ i j hi hj z
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have hj' : Continuous j.symm := continuous_symm j hj
  have hi' : Continuous i.symm := continuous_symm i hi
  have hφ : Continuous (i.trans j.symm) := hj'.comp hi
  have hψ : Continuous (i.trans j.symm).symm := hi'.comp hj
  have hz : Valued.v z < 1 ↔ ‖z‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).symm
  rw [hz, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  constructor
  · intro h
    exact tendsto_pow_map (i.trans j.symm).toRingHom hφ h
  · intro h
    have := tendsto_pow_map (i.trans j.symm).symm.toRingHom hψ h
    simpa using this
end

