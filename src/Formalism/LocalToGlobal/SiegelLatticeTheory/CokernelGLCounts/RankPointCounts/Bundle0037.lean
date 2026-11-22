import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBPf

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.NGCut
  Formalism.L2.SG.NGData

namespace Formalism.L2.SG.NGHTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nDelta {E : Type} [Field E] (r : ℕ) (γ : PN.Pts E r) : ℕ :=
  r * (r + 1) + ∑ a : Fin γ.1.length, endIdx γ a * (2 * r + 1 - endIdx γ a)

def HTPlace : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ {Cl' Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl') (nml : TauC Y u u' → Nu)
        (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl' Nu), FamTie TS cls nml γ Fm →
        (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ≠ 0 ∧ ∀ a, endMin γ a ≠ 0) ∧ ∀ p : PlF D,
        ((Fm.FP p).PrimeTo → (Fm.FP p).Hp = 1) ∧
        (Fm.FP p).Hp =
          ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))) ^ ((2 * D.R.rS + 1 : ℝ) / 2) *
          ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p)) ^ (nDelta D.R.rS γ : ℝ) *
          ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)) ^ (-(1 / 2 : ℝ)) *
          ∏ a : Fin γ.1.length, (((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)))⁻¹

def HTDelta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

def HTTheta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

section Asm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem prod_inf_sq (x : E) : ∏ w : InfinitePlace E, w x ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyComplex.isComplex w).mult_eq_two]

theorem prod_inf (x : E) : ∏ w : InfinitePlace E, w x = Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← prod_inf_sq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => (w.1.nonneg x))]

theorem g_pow (g : ℝ) (hg : 0 < g) (f r : ℕ) :
    ((g ^ (2 * f))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) = (g ^ ((2 * r + 1) * f))⁻¹ := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast g (2 * f), ← Real.rpow_mul hg.le, ← Real.rpow_natCast g]
  congr 2
  push_cast
  ring

theorem inv_rpow_half (x : ℝ) (hx : 0 ≤ x) : (x⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt x := by
  rw [Real.inv_rpow hx, Real.rpow_neg hx, inv_inv, Real.sqrt_eq_rpow]

theorem hpt_eq [StarRing E] (r : ℕ) (γ : PN.Pts E r) (rd g : ℝ) (hg : 0 < g) (TT : ℕ) :
    HPt rd g TT γ =
      ((g ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) *
      ((rd ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ (nDelta r γ : ℝ) *
      (|((Algebra.norm ℚ (GPt TT γ) : ℚ) : ℝ)|⁻¹) ^ (-(1 / 2 : ℝ)) *
      ∏ a : Fin γ.1.length, (|((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹)⁻¹ := by
  set f := Fintype.card (InfinitePlace E) with hf
  rw [g_pow g hg f r, inv_rpow_half _ (abs_nonneg _), Real.rpow_natCast]
  simp only [inv_inv]
  unfold HPt NGPt NDPt
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf]
  have hD : ∀ a : Fin γ.1.length, ∏ w : InfinitePlace E,
      (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 =
      ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f * |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)| := by
    intro a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf_sq]
  simp_rw [hD]
  rw [Finset.prod_mul_distrib]
  have hrd : ((rd ^ (2 * r * (r + 1)))⁻¹) ^ f *
      ∏ a : Fin γ.1.length, ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f =
      ((rd ^ (2 * f))⁻¹) ^ nDelta r γ := by
    simp only [← inv_pow, ← pow_mul, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
    congr 2
    unfold nDelta
    have e : ∀ i : Fin γ.1.length, 2 * (endIdx γ i * (2 * r + 1 - endIdx γ i)) * f =
        2 * f * (endIdx γ i * (2 * r + 1 - endIdx γ i)) := fun i => by ring
    simp only [e, ← Finset.mul_sum]
    ring
  rw [← hrd]
  ring

end Asm

section Main

open Formalism.MainNotions.S.LocNG

theorem hTie_of (hP : HTPlace) (hD : HTDelta) (hT : HTTheta) : Formalism.L2.SG.FamDefs.HTie := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a0, b0, hP2⟩ := hP Cg cb Cw cT CT C0
  refine ⟨a0, b0, ?_⟩
  intro C' Cl e1 e2 D large₂ X Y u u' hc Cl' Nu TS cls nml γ Fm hFT
  obtain ⟨⟨hG0, hD0⟩, hloc⟩ := hP2 C' Cl e1 e2 D large₂ X Y u u' hc TS cls nml γ Fm hFT
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, -, -, -, hgood, -⟩ := hFT
  have hOK : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hPF := (product_formula_e D.host.F D.host.E _ (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.s.atP).1 (zOf Y).M hOK
  obtain ⟨hAf, hAv⟩ := hT D (zOf Y)
  obtain ⟨hBf, hBv⟩ := hD D (zOf Y)
  obtain ⟨hCf, hCv⟩ := hPF _ hG0
  have hDf := fun a => hPF _ (hD0 a)
  classical
  set S : Finset (PlF D) := Fm.P ∪ hAf.toFinset ∪ hBf.toFinset ∪ hCf.toFinset ∪
    Finset.univ.biUnion (fun a => (hDf a).1.toFinset) with hS
  have hPS : Fm.P ⊆ S := fun p hp => by simp [hS, hp]
  have hsA : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p)))) ⊆ ↑S := fun p hp => by
    simp [hS, Set.Finite.mem_toFinset, hp]
  have hsB : (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsC : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsD : ∀ a, (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a))) ⊆ ↑S :=
    fun a p hp => by
      simp only [hS, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_union, Set.mem_iUnion,
        Set.Finite.coe_toFinset, Set.mem_univ, true_and]
      exact Or.inr ⟨a, trivial, hp⟩
  have hnn : ∀ p (x : (D.s.atP p).Ep), 0 ≤ ((zOf Y).M p).modK x := fun p x => ENNReal.toReal_nonneg

  have h1 : Fm.toL.Htot = ∏ p ∈ S, (Fm.FP p).Hp := by
    show ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp = _
    rw [Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp)]
    exact Finset.prod_subset hPS fun p _ hp => (hloc p).1 (hgood p hp)
  rw [h1, Finset.prod_congr rfl fun p _ => (hloc p).2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_comm (s := S) (t := Finset.univ),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))))
      (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)))
      (fun p _ => hnn p _)]
  simp_rw [Finset.prod_inv_distrib]
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsA, ← finprod_eq_prod_of_mulSupport_subset _ hsB,
    ← finprod_eq_prod_of_mulSupport_subset _ hsC, hAv, hBv, hCv]
  have hDv : ∀ a, ∏ p ∈ S, ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)) =
      |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹ := fun a => by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (hsD a), (hDf a).2]
  simp_rw [hDv]
  have hg : (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    exact_mod_cast Nat.mul_pos h0 h1
  have hXg : (X.B.g : ℝ) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by rw [X.g_eq]
  rw [hXg, ← Finset.prod_inv_distrib]
  exact hpt_eq D.R.rS γ D.host.rdE _ hg _

end Main

end Formalism.L2.SG.NGHTie
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowsInputPOfTermsFiniteSig
section
noncomputable section

namespace Formalism.L2.SG.DataCut

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped ComplexOrder

def RowsDatumP (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
      (∀ d ∈ densSet L δ ϖ u u' F0 what₂, 0 ≤ d) ∧
      ∃ (th : TermDef.Term D u u' F0 what₂ → ∀ p, Option ((M p).Cls D.R.rS)) (dn : TermDef.Term D u u' F0 what₂ → ℝ),
        (∀ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
          (∀ w, ∃ S : Finset (PlF D), Formalism.L2.SG.Pf.UnramOff M δ (D.mem u).A.T (D.mem u').A.T θ0 S w) →
          ∀ γ w, EligAt γ w → Formalism.L2.SG.Pf.Restricted θ0 (th γ)) ∧
        (∀ γ w, EligAt γ w → dn γ ∈ densSet L δ ϖ u u' F0 what₂) ∧
        PartnerSumC δ M (PairVal.vRdef D u u' F0 what₂ δ M) th ∧
        FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) nc th dn

def RowsDomAtP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
    ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
    ∀ Y : Finset (TB.Pt D.host.E), (∀ p ∈ Y, TB.IsPt p ((dOf S δ M u u').r + 1)) →
      TB.PSDOn Y (fun p q => ((supDens L δ ϖ u u' F0 what₂ / α : ℝ) : ℂ) *
          (dOf S δ M u u').Kr ((dOf S δ M u u').r + 1) p q -
        rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) p q)

def RowsInputP (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
      (∃ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ) ∧
      ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
        RowsPSD S δ M L u u' F0 what₂ ϖ (PairVal.vRdef D u u' F0 what₂ δ M) κ nc α

section P

variable {D : Formalism.BasicNotions.D7}

theorem rowsDomAtP_of (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsDomAtP D := by
  classical
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY
  obtain ⟨hdens0, th, dn, hres, hdnS, hPS, hFC⟩ := hRD hsig δ M hA L u u' hT hPH F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨θ0, hU⟩ := hTU δ M hA (D.mem u).A.T (D.mem u').A.T
  set sd := supDens L δ ϖ u u' F0 what₂ with hsdd
  have hsd0 : 0 ≤ sd := Real.sSup_nonneg (fun d hd => hdens0 d hd)
  have hdn : ∀ γ w, EligAt γ w → dn γ ≤ sd := fun γ w h => le_csSup hbdd (hdnS γ w h)
  have hFC' : FiberCntC δ M (PairVal.vRdef D u u' F0 what₂ δ M) (nc * α) th (fun γ => dn γ / α) := by
    intro w hG γ₀ w₀ h0
    have e : (n0 (nc * α) (D.mem u).A.T (D.mem u').A.T w : ℂ) * ((dn γ₀ / α : ℝ) : ℂ) =
        (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dn γ₀ : ℂ) := by
      unfold n0
      push_cast
      field_simp
      try ring
    rw [e]
    exact hFC w hG γ₀ w₀ h0
  have hnc' : 0 < nc * α := mul_pos hnc.1 hα

  let pt0 : Point D.host.E (D.R.rS + 1) := ⟨[(1, D.R.rS + 1)], by simp, by simp⟩
  let wOf : Y → Point D.host.E (D.R.rS + 1) := fun x => (ptOfList (D.R.rS + 1) x.1).getD pt0
  have hP := dom_points hN hA hrows hnc' (PairVal.vRdef D u u' F0 what₂ δ M) hκ (hTF u u') hsig hU (hres θ0 (fun w => (hU w).1))
    (sd / α) (div_nonneg hsd0 hα.le) (fun γ w h => div_le_div_of_nonneg_right (hdn γ w h) hα.le) hPS hFC' wOf
  let φi : Y → ℂ := fun x => if (ptOfList (D.R.rS + 1) x.1).isSome then ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ else 0
  have hr : (dOf S δ M u u').r = D.R.rS := hC.1
  unfold TB.PSDOn
  rw [hr]
  have key : (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) * (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 -
      rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1) =
      (Matrix.diagonal φi).conjTranspose * (Matrix.of fun x y : Y => ((sd / α : ℝ) : ℂ) *
        KtopG M δ (D.mem u).A.T (D.mem u').A.T (wOf x) (wOf y) -
        ∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf x) *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ (wOf y))) * Matrix.diagonal φi := by
    ext x y
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
    show _ = star (φi x) * _ * φi y
    rcases hx : ptOfList (D.R.rS + 1) x.1 with _ | wx
    · have h0 : φi x = 0 := by simp [φi, hx]
      rw [h0, star_zero, zero_mul, zero_mul]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hx]
      rw [hK, hR]
      simp
    rcases hy : ptOfList (D.R.rS + 1) y.1 with _ | wy
    · have h0 : φi y = 0 := by simp [φi, hy]
      rw [h0, mul_zero]
      have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = 0 := by
        show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = 0
        unfold KrOf
        rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 = 0 := by
        unfold rowKer
        simp [rowVec, hy]
      rw [hK, hR]
      simp
    have hwx : wOf x = wx := by simp [wOf, hx]
    have hwy : wOf y = wy := by simp [wOf, hy]
    have hφx : φi x = ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hx]
    have hφy : φi y = ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)⁻¹ := by simp [φi, hy]
    have hx' : Formalism.L2.S.IsPtL x.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hx
    have hy' : Formalism.L2.S.IsPtL y.1 (D.R.rS + 1) := by
      by_contra hn
      simp [ptOfList, isPtL_signPt, hn] at hy
    have hpx : ((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hx').ne'
    have hpy : ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (phi_pos hy').ne'
    have hK : (dOf S δ M u u').Kr (D.R.rS + 1) x.1 y.1 = KtopG M δ (D.mem u).A.T (D.mem u').A.T wx wy /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      show KrOf δ M (D.mem u).A.T (D.mem u').A.T (D.R.rS + 1) x.1 y.1 = _
      unfold KrOf
      rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hx, hy]
      simp only
      rw [Kglob, dif_pos rfl]
    have hR : rowKer (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) x.1 y.1 =
        (∑' ρ, chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wx *
          star (chat (PairVal.vRdef D u u' F0 what₂ δ M) κ (nc * α) ρ wy)) /
        (((phi (D.R.rS + 1) x.1 : ℝ) : ℂ) * ((phi (D.R.rS + 1) y.1 : ℝ) : ℂ)) := by
      unfold rowKer
      rw [← tsum_div_const]
      refine tsum_congr fun ρ => ?_
      rw [rowVec_eq_chat _ _ _ ρ x.1 wx hx, rowVec_eq_chat _ _ _ ρ y.1 wy hy]
      simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
      field_simp
    rw [hK, hR, hwx, hwy, hφx, hφy]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [key]
  exact hP.conjTranspose_mul_mul_same _

theorem rowsInputP_of (hG : Corank.ScalarEquivG) (hR : ∀ u u' : D.what₂.Word, Corank.ScalarRepFree D u u')
    (hF : RowsFinAt D) (hDm : RowsDomAtP D) : RowsInputP D := by
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd
  refine ⟨rowLabelExists_of hG hR u u' F0 what₂ hrows, fun κ hκ => ?_⟩
  intro Y hY R
  exact psdOn_of_full Y _ _ (fun x => hF δ M hA u u' hT F0 what₂ hrows (nc * α) κ hκ x)
    (hDm Wp Wq S δ M hA L u u' hT hPH hC F0 what₂ hrows ϖ hϖ nc hnc α hα hbdd κ hκ Y hY) R

theorem rowsInputP_of_termsFinite_sig (hN : SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D)
    (hTF : ∀ u u' : D.what₂.Word, TermDef.TermsAtFinite D u u') (hsig : (VS D).SigOK) : RowsInputP D :=
  rowsInputP_of Formalism.L2.SG.Closed.ScalarEquivG_holds
    (fun u u' => Formalism.L2.SG.Closed.ScalarRepFree_holds (D := D) (u := u) (u' := u'))
    (rowsFinAt_of hTF hsig) (rowsDomAtP_of hN hTU hRD hTF hsig)

theorem rowsInputP_of_normProd_topUnram (hN : Formalism.L2.SG.SupportG.NormProd D) (hTU : TopUnram D) (hRD : RowsDatumP D) :
    RowsInputP D :=
  rowsInputP_of_termsFinite_sig hN hTU hRD (fun u u' => terms_at_point_finite D u u') (PI.TermsAtPtFiniteW.sigOK_holds D)

theorem rowsInputP_of_normProd (hN : Formalism.L2.SG.SupportG.NormProd D) (hRD : RowsDatumP D) : RowsInputP D :=
  rowsInputP_of_normProd_topUnram hN (Formalism.L2.SG.Pf.topUnram_holds D) hRD

theorem rowsInputAt_of_P (h : RowsInputP D)
    (hPH : ∀ u u' : D.what₂.Word, Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) :
    Formalism.L2.SG.DataInst.RowsInputAt D := by
  unfold Formalism.L2.SG.DataInst.RowsInputAt
  intros
  apply h <;> first | assumption | exact hPH _ _

end P

end Formalism.L2.SG.DataCut

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical ValuativeRel

theorem rowsDatumP_of {D : Formalism.BasicNotions.D7}
    (h : (VS D).SigOK → ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
      (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') →
      ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
        IsRowReps D F0 what₂ → CutAt M δ L u u' F0 what₂) :
    RowsDatumP D := by
  intro hsig δ M hA L u u' hc hPH F0 what₂ hRo ϖ hϖ nc hnc
  exact rowsDatum_at (h hsig δ M hA L u u' hc hPH F0 what₂ hRo)
    (eligFinite_of (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') hsig hRo) hRo ϖ hϖ nc hnc

end Formalism.L2.SG.LsDatumB
end
end

