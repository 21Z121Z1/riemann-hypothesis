import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

def etI (e : ETEx h P Arch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) : ℕ := (e j h1 h2).choose

def etF (e : ETEx h P Arch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) :
    (recB h.toLawsCore).Cusp j (wEt D j (etI e j h1 h2)) :=
  (e j h1 h2).choose_spec.2.choose

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T)

theorem combAlg_of_combBound (j : ℕ) (hj : InR D j) (hjm : j < D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (cb / (2 * (G.iet : ℝ))) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := y0.2
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz
  let y : T.PtA j la := PtV.mk la ho z hz η hη
  have hyv : vAtV y = vAtV y0 := funext fun g => by
    show y.1.1 g = y0.1.1 g
    rw [hq]
    rfl
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hyv]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  obtain ⟨h0, h1⟩ := (hX la y).1 hjm
  rw [hv] at h0 h1
  rw [hd] at h1
  refine ⟨h0, fun htop => ?_⟩
  have h2 := h1 htop
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)] at h2
  exact h2

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def extAll : PtExt (recPJ h j hj) where
  Pt' la := valSet (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) la
  extendedPointBaseChange la _ := (T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).yEta
    (Classical.choice ((T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).genNe _))
  vAt' _ y := vG y.1
  vAt'_zero la y := vG_zero (isVal_valSet la y.1 y.2).zero
  vAt'_ne_bot la y := vG_ne_bot (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).ne_bot
  vAt'_add la y := vG_add (isVal_valSet la y.1 y.2).add
  vAt'_smul la y a F ha := vG_smul (fun r => (isVal_valSet la y.1 y.2).smul a r ha) F
  vAt'_mul la y := vG_mul deg (cutR T.C j) (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).mul

theorem extAll_vAt_inc (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (extAll h j hj).Pt' la) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 := by

  have hinc : ∀ m, ((recPJ h j hj).inc w F).coeff m = if deg w = m then F.1 else 0 := by
    intro m
    show (AddMonoidAlgebra.single (deg w) _).coeff m = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have h0 : y.1 0 = ⊤ := by
    first
      | exact (isVal_valSet la y.1 y.2).zero
      | simpa using (isVal_valSet la y.1 y.2).zero
  show vG y.1 ((recPJ h j hj).inc w F) = y.1 F.1
  unfold vG
  simp only [hinc]
  apply le_antisymm
  · exact iInf_le_of_le (deg w) (by simp)
  · refine le_iInf fun m => ?_
    split_ifs with hm
    · exact le_rfl
    · rw [h0]
      exact le_top

theorem intAtExt_extAll : IntAtExt _ (extAll h j hj) := by
  intro w F hF la y
  rw [extAll_vAt_inc]
  exact (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) hF la y.1 y.2

def recPlus : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j := xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.InvProofs
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem levelK_unique {V : HSp D} {N : ℕ} {Kf Kf' : Subgroup (GA D V)} (h : IsLevelK V N Kf)
    (h' : IsLevelK V N Kf') : Kf = Kf' :=
  Subgroup.ext fun k => (h k).trans (h' k).symm

def RdUIndep (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ →
    ∀ (U U' : Unf (Q.Xo j) Q.c σ D.R.r), IsUnf U → IsUnf U' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (Q.Xo j) Q.c a n,
      (rdU U f ∈ holSub U.X (laU U a n) ↔ rdU U' f ∈ holSub U'.X (laU U' a n)) ∧
      (rdU U f ∈ holSub U.X (laU U a n) →
        supN U.X (laU U a n) (rdU U f) = supN U'.X (laU U' a n) (rdU U' f))

def L2Independence (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r),
    (∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) → (∀ σ, GoodEmb Q.c σ → IsUnf (U' σ)) →
    ∀ (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ (V : HSp D), V = D.sp.W j → ∀ (Kf : Subgroup (GA D V)),
      IsLevelK V (D.host.g 0 * D.host.g 1) Kf → FinVol V →
    ∀ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (dict' : GA D V → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
      (mu mu' : GA D V → ℂ),
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr) →
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict' Kf th hr) →
      MuUnit V dict mu → MuUnit V dict' mu' → Continuous mu → Continuous mu' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (hl : JMemL2 V σ (rdC U σ a n) dict mu) (hl' : JMemL2 V σ (rdC U' σ a n) dict' mu')
      (f : Rul (Q.Xo j) Q.c), f ∈ cusp (Q.Xo j) Q.c U a n → f ∈ cusp (Q.Xo j) Q.c U' a n →
      l2C U σ V dict mu (xiR D) a n hl f = l2C U' σ V dict' mu' (xiR D) a n hl' f

theorem l2_independent_two_spaces (hL : L2Independence D) (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r)
    (hU : ∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) (hU' : ∀ σ, GoodEmb Q.c σ → IsUnf (U' σ))
    (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (V1 V2 : HSp D) (hV1 : V1 = D.sp.W j) (hV2 : V2 = D.sp.W j)
    (Kf1 : Subgroup (GA D V1)) (Kf2 : Subgroup (GA D V2))
    (hK1 : IsLevelK V1 (D.host.g 0 * D.host.g 1) Kf1) (hK2 : IsLevelK V2 (D.host.g 0 * D.host.g 1) Kf2)
    (hF : FinVol V1)
    (dict : GA D V1 → Σ k, Frame ((U σ).X k).Ψ D.R.r) (dict' : GA D V2 → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
    (mu : GA D V1 → ℂ) (mu' : GA D V2 → ℂ)
    (hd : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V1 dict Kf1 th hr)
    (hd' : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V2 dict' Kf2 th hr)
    (hm : MuUnit V1 dict mu) (hm' : MuUnit V2 dict' mu') (hc : Continuous mu) (hc' : Continuous mu')
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (hl : JMemL2 V1 σ (rdC U σ a n) dict mu) (hl' : JMemL2 V2 σ (rdC U' σ a n) dict' mu')
    (f : Rul (Q.Xo j) Q.c) (hf : f ∈ cusp (Q.Xo j) Q.c U a n) (hf' : f ∈ cusp (Q.Xo j) Q.c U' a n) :
    l2C U σ V1 dict mu (xiR D) a n hl f = l2C U' σ V2 dict' mu' (xiR D) a n hl' f := by
  subst hV1
  subst hV2
  obtain rfl := levelK_unique hK1 hK2
  exact hL Q j U U' hU hU' σ hσ _ rfl Kf1 hK1 hF dict dict' mu mu' hd hd' hm hm' hc hc' a n hdom hl hl' f hf hf'

theorem cusp_eq_of_rd (hR : RdUIndep D) (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r)
    (hU : ∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) (hU' : ∀ σ, GoodEmb Q.c σ → IsUnf (U' σ))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) :
    cusp (Q.Xo j) Q.c U a n = cusp (Q.Xo j) Q.c U' a n := by
  ext f
  rw [mem_cusp, mem_cusp]
  refine and_congr_right fun hf => forall_congr' fun σ => forall_congr' fun hσ => ?_
  exact (hR Q j σ hσ (U σ) (U' σ) (hU σ hσ) (hU' σ hσ) a n hdom f hf).1

theorem cxIndep_of (hR : RdUIndep D) (hL : L2Independence D) : CxIndep D := by
  intro T U V dict mu Kf h h' j hj w
  have hU : ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ) := h.unf j hj
  have hU' : ∀ σ, GoodEmb T.Q.c σ → IsUnf (U j σ) := h'.unf j hj
  have hC : T.C j w = Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w :=
    cusp_eq_of_rd hR T.Q j (T.U j) (U j) hU hU' (wtA w) w.n (dom_wtA w)
  refine ⟨hC, fun σ f hf => ⟨?_, ?_⟩⟩
  · have hσ := goodEmb_goodOf T.Q.c σ
    have hmem := ((mem_cusp _ _ _ _ _ f).1 hf).2 _ hσ
    have hsec := ((mem_cusp _ _ _ _ _ f).1 hf).1
    have e := (hR T.Q j _ hσ (T.U j _) (U j _) (hU _ hσ) (hU' _ hσ) (wtA w) w.n (dom_wtA w) f hsec).2 hmem
    show supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n f =
      supC (T.Q.Xo j) T.Q.c (U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n f
    unfold supC
    rw [e]
  · have hσ := goodEmb_goodOf T.Q.c σ
    have hf' : f ∈ Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w := hC ▸ hf
    unfold NlM
    rw [dif_pos hj, dif_pos hj]
    exact l2_independent_two_spaces hL T.Q j (T.U j) (U j) hU hU' _ hσ _ _ (h.spaceW j hj _ hσ) (h'.spaceW j hj _ hσ)
      _ _ (h.levelK j hj _ hσ) (h'.levelK j hj _ hσ) (h.finVol j hj _ hσ) _ _ _ _
      (h.dictU j hj _ hσ) (h'.dictU j hj _ hσ) (h.muUnit j hj _ hσ) (h'.muUnit j hj _ hσ)
      (h.muCont j hj _ hσ) (h'.muCont j hj _ hσ) (wtA w) w.n (dom_wtA w) _ _ f hf hf'

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.KsCore
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

namespace KsCore

variable {D : D7} (T : Core D)

abbrev WK (j : ℕ) (κ : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.C j κ

def MK (j : ℕ) (κ : WeightFamilies.Wt D j) :=
  latOf (T.C j κ) (T.Vs j) (fun la => isVal_valSet la)

def bW (h : LawsCore T) (j : ℕ) (hj : InR D j) (κ : WeightFamilies.Wt D j) :
    Module.Basis (Fin (Module.finrank T.Q.c.F (WK T j κ))) T.Q.c.F (WK T j κ) :=
  haveI := h.fd j hj κ
  haveI : Module.Free T.Q.c.F (WK T j κ) := Module.Free.of_divisionRing _ _
  Module.finBasis T.Q.c.F (WK T j κ)

def coordL {ι : Type} (L : Type) [Field L] [Algebra T.Q.c.F L] {j : ℕ} {κ : WeightFamilies.Wt D j}
    (b : Module.Basis ι T.Q.c.F (WK T j κ)) : WK T j κ →ₗ[T.Q.c.F] (ι → L) :=
  (LinearMap.compLeft (Algebra.linearMap T.Q.c.F L) ι).comp (Finsupp.lcoeFun.comp b.repr.toLinearMap)

variable {G : Type} [Group G]

def KeepsCu (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) : Prop :=
  ∀ g, ∀ f ∈ T.C j κ, actLev (Xo := T.Q.Xo j) T.Q.c lev g f ∈ T.C j κ

open Classical in

def rhoGeo (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) :
    G →* Module.End T.Q.c.F (WK T j κ) :=
  if h : ActLev (Xo := T.Q.Xo j) T.Q.c lev ∧ KeepsCu T j κ lev then
    { toFun := fun g => (actLev (Xo := T.Q.Xo j) T.Q.c lev g).restrict (h.2 g)
      map_one' := by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_one _ _ _ h.1.total h.1.func h.1.one (cusp_le_sec _ _ _ _ _ f.2).1
      map_mul' := by
        intro g g'
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_mul _ _ _ h.1.total h.1.func h.1.mul g g' (cusp_le_sec _ _ _ _ _ f.2).1 }
  else 1

set_option synthInstance.maxHeartbeats 400000 in

def actT (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))
    (χ : G →* (T.Q.c.F)ˣ) (g : G) : Module.End T.Q.c.F (WK T j κ) :=
  ((χ g)⁻¹ : (T.Q.c.F)ˣ).val • rhoGeo T j κ lev g

set_option synthInstance.maxHeartbeats 400000 in

def eOf [Fintype G] (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))
    (χ : G →* (T.Q.c.F)ˣ) (eg : G → T.Q.c.F) : Module.End T.Q.c.F (WK T j κ) :=
  ∑ g, eg g • actT T j κ lev χ g

abbrev nrm (j : ℕ) (κ : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ := T.Ns j κ σ

end KsCore

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftInSt
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def HdIntAt {y : PtsG G la → E.Pt' la} (hs : ∀ ζ, SecPt ζ (y ζ)) (x : Lw (xplus X E hM) la G.w) : Prop :=
  ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
    0 ≤ nval (hs ζ).T.V 1 ((hs ζ).lift (l.foldr (fun β z => hasse (xplus X E hM) la G.w β z) x))

def LocRingSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)) ∧
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftUnit
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

theorem isUnit_toOsK_of_lift {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ)) (C : CurveModel G la g0)
    (x : ↥(Frac0 (xplus X E hM) la G.w))
    (hx : ∀ ζ, (hw ζ).toSecPt.lift (x : Lw (xplus X E hM) la G.w) ≠ 0) :
    IsUnit (toOsK (xplus X E hM) la G.w x) := by
  classical
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
    exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv
  have : IsReduced (OsK (xplus X E hM) la G.w) := by
    have : IsReduced (↥C.A' ⧸ C.JA) := C.red
    exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective
  have : IsArtinianRing (OsK (xplus X E hM) la G.w) := IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _
  by_contra hnu
  set a := toOsK (xplus X E hM) la G.w x with ha
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum (OsK (xplus X E hM) la G.w), a ∈ I.asIdeal := by
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact ⟨⟨M, hM⟩, haM (Ideal.subset_span rfl)⟩
  let e := IsArtinianRing.equivPi (OsK (xplus X E hM) la G.w)
  set ε := e.symm (Pi.single I 1) with hε
  have hεa : ε * a = 0 := by
    apply e.injective
    rw [map_mul, map_zero, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm
      rw [Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]
      show Ideal.Quotient.mk m.asIdeal a = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hI
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul, Pi.zero_apply]
  have hεε : ε * ε = ε := by
    apply e.injective
    rw [map_mul, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm; rw [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul]
  have hε0 : ε ≠ 0 := by
    intro h
    have h1 := congrArg e h
    rw [hε, e.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 I
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    have h3 : (1 : OsK (xplus X E hM) la G.w) ∈ I.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h2)
    exact I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hint : IsIntegral (Op (xplus X E hM) la G.N) ε := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [pow_two, hεε]
  let ε' : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ⟨ε, hint⟩
  have hnot : ¬ IsUnit (1 - ε') := by
    intro hu
    apply hε0
    have h1 : ε' * (1 - ε') = 0 := by
      apply Subtype.ext
      show ε * (1 - ε) = 0
      rw [mul_sub, mul_one, hεε, sub_self]
    have h2 := (hu.mul_left_eq_zero).1 h1
    exact congrArg Subtype.val h2
  obtain ⟨Z, hZ, hZ1⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ε'}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  let ζ : PtsG G la := ⟨Z, hZ⟩
  have hεZ : ε' ∉ ζ.asIdeal := by
    intro h
    have h1 : (1 - ε') + ε' ∈ Z := Z.add_mem (hZ1 (Ideal.subset_span rfl)) h
    rw [sub_add_cancel] at h1
    exact hZ.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨e0, he0⟩ := toOsK_surjective (xplus X E hM) la G.w ε
  have hev := (hw ζ).evW e0 ε' he0
  have hu : IsUnit (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) ε') :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal ε').2 hεZ
  have hne : (hw ζ).toSecPt.lift (e0 : Lw (xplus X E hM) la G.w) ≠ 0 := by
    rw [hev]
    exact ((hu.map (hw ζ).ι).map (algebraMap (hw ζ).T.V (hw ζ).T.Fr)).ne_zero
  have hJ : e0 * x ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_mul, he0]
    exact hεa
  have h0 := (hw ζ).toSecPt.lift_Jid hJ
  rw [Subalgebra.coe_mul, map_mul] at h0
  exact mul_ne_zero hne (hx ζ) h0

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

theorem prodInLat_of (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hka : ∀ x, wtA ka x = n * wtA wL x) (hkn : ka.n = n * wL.n) : ProdInLat hL j ka wR n := by
  have hV : ∀ la, ∀ v ∈ Tc.Vs j la, IsVal la v := fun la => isVal_valSet la
  have hw1 : ∀ k, wR k ∈ Tc.C j wL ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (wR k) := by
    intro k
    obtain ⟨F, hF, hFk⟩ := hw k
    rw [← hFk]
    exact ⟨cutR_le Tc.C j wL F.2, hF⟩
  have key : ∀ m (s : Fin (m + 1) → Fin (N + 1)), ∃ W : WeightFamilies.Wt D j, (∀ x, wtA W x = (m + 1) * wtA wL x) ∧
      W.n = (m + 1) * wL.n ∧ ∏ k, wR (s k) ∈ Tc.C j W ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (∏ k, wR (s k)) := by
    intro m
    induction m with
    | zero =>
      intro s
      refine ⟨wL, fun x => by ring, by ring, ?_, ?_⟩
      · rw [Fin.prod_univ_one]; exact (hw1 _).1
      · rw [Fin.prod_univ_one]; exact (hw1 _).2
    | succ m ih =>
      intro s
      obtain ⟨W, hW1, hW2, hWm, hWv⟩ := ih (fun k => s k.succ)
      refine ⟨WeightAlgebra.wadd wL W, fun x => ?_, ?_, ?_, ?_⟩
      · rw [wtA_wadd, Pi.add_apply, hW1 x]; ring
      · rw [n_wadd, hW2]; ring
      · rw [Fin.prod_univ_succ]; exact hL.mul j hj wL W _ (hw1 _).1 _ hWm
      · intro la v hv
        rw [Fin.prod_univ_succ, (hV la v hv).mul]
        exact add_nonneg ((hw1 _).2 la v hv) (hWv la v hv)
  intro s
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W, hW1, hW2, hWm, hWv⟩ := key m s
  have hmem : ∏ k, wR (s k) ∈ Tc.C j ka := by
    have hC : Tc.C j ka = Tc.C j W := by
      show Tc.cuspA j (wtA ka) ka.n = Tc.cuspA j (wtA W) W.n
      rw [hkn, hW2, show wtA ka = wtA W from funext fun x => by rw [hka x, hW1 x]]
    rw [hC]; exact hWm
  refine ⟨⟨∏ k, wR (s k), ?_⟩, ?_, rfl⟩
  · show _ ∈ cutR Tc.C j ka
    rw [cutR_eq Tc.C hj]; exact hmem
  · exact hWv

theorem prodInLat_of_wtZ (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hkaZ : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) : ProdInLat hL j ka wR n := by
  refine prodInLat_of hL j hj wR wL ka n hw hn (fun x => ?_) ?_
  · have h1 := congrFun (congrArg Prod.fst hkaZ) x
    simp only [wtZ, Prod.smul_fst, Pi.smul_apply] at h1
    rw [nsmul_eq_mul] at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd hkaZ
    simp only [wtZ, Prod.smul_snd] at h2
    rw [nsmul_eq_mul] at h2
    exact_mod_cast h2

end Formalism.L2.Pj
end
end

