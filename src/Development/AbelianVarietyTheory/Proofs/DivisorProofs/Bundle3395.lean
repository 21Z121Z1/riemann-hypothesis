import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HSApp

section Gen

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

set_option maxHeartbeats 2000000 in

theorem exists_semilinear_L2_independent (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : FDSec (U σ).X,
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
    show ‖mu q.out * P (dict q.out).1 (dict q.out).2‖ = _
    rw [norm_mul, hmu1, one_mul, Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _), GlobalTheory.AllWt.ptN,
      pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    ⟨aesm_of_holSub hm _ P.2, by
      rw [heq]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)⟩
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add, map_add]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add, smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]

end Gen

set_option maxHeartbeats 2000000 in

theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (GlobalTheory.CovTop.PetRep.adelMeas_one_of_good Y hY _ hσ') (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_pos h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_neg h))

set_option maxHeartbeats 1000000 in

theorem goodAt_of_gapGe : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → Y.GoodAt (wtOf _ la 0) := by
  intro hP D T j Y e o hY hf la hla
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY (wtOf _ la 0)
  exact ⟨hasGram_nrm_of_good D T j Y e o hY _, GlobalTheory.T.weight_lattice_finitely_generated hP D T j Y e o hY hf la hla hfd,
    GlobalTheory.T.weight_lattice_span_eq_top hP D T j Y e o hY hf la hla hfd⟩

theorem goodAt_hs : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ P : WtPar (T.Q.Dw j), WtBig P →
      Y.GoodAt (wtOf _ P.u₁ 0) ∧ Y.GoodAt (wtOf _ P.u₂ 0) ∧ ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0) := by
  intro hP D T j Y e o hY hf P hB
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HSApp.GapArith.gaps_main _ _ _ P hB
  exact ⟨goodAt_of_gapGe hP D T j Y e o hY hf _ h1, goodAt_of_gapGe hP D T j Y e o hY hf _ h2,
    fun i _ => goodAt_of_gapGe hP D T j Y e o hY hf _ (h3 i)⟩

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquare
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaSquare
open GlobalTheory.SymLiftOdd GlobalTheory.UT.SymFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem eq_liftFun_mul (hL : L.IsLB) {k : ℤ} (s s' : LB.Sec (LPow A L k T)) (a : Γ(T.left, ⊤))
    (h : ∀ y J, Good L y J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y J =
        gs (fst T A).left y ⊤ a * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y J)
    (j) : s'.f j = liftFun A _ a * s.f j := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have e₁ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₂ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (liftFun A ((LPow A L k T).U j) a) = gs (fst T A).left y ⊤ a :=
    (gs_res (𝟙 _) y le_top hy _).trans ((gs_pull (𝟙 _) (fst T A).left y ⊤ trivial a).trans (by rw [Category.id_comp]))
  refine e₁.trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  exact (congrArg _ (h y I hI)).trans (mul_left_comm _ _ _)

theorem indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {P v} (h : GRep L (T ⊗ A) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), P U h = 1) (m m' : T ⊗ A ⟶ A)
    (y : (T ⊗ A).left) (J) (hJ : Good L y J) : v _ (lift (fst T A) m) y J = v _ (lift (fst T A) m') y J := by
  obtain ⟨K, _, φ, ε, s, hs, p, hv⟩ := h
  obtain ⟨a, ha⟩ := exists_constT hG hA hL (fun U _ h => (p U h).trans (hP U h)) hs
  exact (hv _ _ y J hJ).symm.trans ((ha m y J hJ).trans ((ha m' y J hJ).symm.trans (hv _ _ y J hJ)))

theorem grep_sigma {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    {Y : Over S} (w : Y ⟶ A) :
    GRep L Y (fun _ _ h => h (w⁻¹).left * (h w.left)⁻¹) (fun _ r z J => val σ (r ≫ w).left z J) :=
  (grep_gen σ hσ w.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (w⁻¹).left ^ (1 : ℤ) * h (w.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_two {n : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, n.left] ![a, b])} (hα : α.IsGen) (w : T ⊗ A ⟶ A) :
    GRep L (T ⊗ A) (fun _ _ h => h w.left ^ a * h (lift (fst T A) w ≫ n).left ^ b)
      (fun _ r z J => val α (r ≫ lift (fst T A) w).left z J) :=
  (grep_gen α hα (lift (fst T A) w).left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (lift (fst T A) w ≫ snd T A).left ^ a * h (lift (fst T A) w ≫ n).left ^ b = _
      rw [lift_snd])
    (fun _ _ _ _ _ => rfl)

theorem square_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    (hσ₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ σ (eSec A)) (LB.oneGen L))
    (θ : ThetaGrp A L ((4 : ℕ) : ℤ) T) (hx : θ.pt ^ 4 = 1) (nu : LB.Gen (negLB A L ((4 : ℕ) : ℤ) T))
    (hnu : ∀ y J, Good L y J → ∀ m, negVal nu y J m = (val σ m.left y J ^ 4)⁻¹)
    (hs : LB.Gen.Corr L _ _ _ _ (symGen A L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen L))
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ 2).left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])}
    (hα : α.IsGen) (y : (T ⊗ A).left) (J) (hJ : Good L y J) :
    thetaVal θ y J (snd T A) * (thetaVal θ y J ((fst T A ≫ θ.pt) * snd T A) *
      val α (lift (fst T A) ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))).left y J) =
      val σ ((fst T A ≫ θ.pt) ^ 2).left y J * val α (lift (fst T A) (snd T A)).left y J := by
  have := hA.comm
  have hX : (fst T A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have s₁ : val σ (1 : T ⊗ A ⟶ A).left y J = 1 :=
    (val_pull hJ σ (eSec A) (T ⊗ A).hom).symm.trans ((val_corr hJ hσ₁ _).trans (val_one _))
  have sy := (val_symGen θ nu rfl hJ 1).symm.trans ((val_corr hJ hs _).trans (val_one _))
  rw [hnu y J hJ, hnu y J hJ, s₁, _root_.mul_one, inv_one] at sy
  have gθ := fun w => grep_two (L := L) (n := translPt A θ.pt) (a := ((4 : ℕ) : ℤ)) (b := -((4 : ℕ) : ℤ))
    (α := θ.φ) θ.isGen w
  have cl : ∀ m w : T ⊗ A ⟶ A, lift (fst T A) m ≫ lift (fst T A) w = lift (fst T A) (lift (fst T A) m ≫ w) :=
    fun m w => by rw [comp_lift, lift_fst]
  have H₁ := indep hG hA hL (((gθ (snd T A)).mul ((gθ ((fst T A ≫ θ.pt) * snd T A)).mul
    (grep_two hα ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))))).mul (grep_two hα (snd T A)).inv)
    (fun U _ h => by
      have e : ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A)) ^ 2 = snd T A ^ 2 := by
        rw [← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
      simp only [lift_translPt, MonObj.comp_pow, lift_snd, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (snd T A) (fst T A ≫ θ.pt)⁻¹ y J hJ
  have H₂ := indep hG hA hL ((((grep_sigma hσ (snd T A)⁻¹).pow 4).inv.mul ((grep_two hα (snd T A)).mul
    (grep_two hα (snd T A)⁻¹).inv)).mul (grep_sigma hσ (snd T A ^ 2)).inv)
    (fun U _ h => by
      simp only [MonObj.comp_pow, lift_snd, inv_inv, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) (fst T A ≫ θ.pt) 1 y J hJ
  simp only [cl, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, lift_snd, lift_fst_assoc, mul_inv_cancel, _root_.mul_one,
    inv_one, one_pow, s₁] at H₁ H₂
  replace H₁ := congrArg Additive.ofMul H₁
  replace H₂ := congrArg Additive.ofMul H₂
  replace sy := congrArg Additive.ofMul sy
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, thetaVal] at H₁ H₂ sy ⊢
  linear_combination (norm := module) H₁ + H₂ + sy

theorem exists_symmetric_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  intro R _ _ A F _ _ _ x hx σ hσ hσ₁
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hL := A.isLB
  have := A.isAb.comm
  obtain ⟨θ₀, h₀⟩ := GlobalTheory.ThetaLift.exists_theta_of_field (FractionRing R) A (TFK (R := R) F) F (Iso.refl _) 4 x hx
  obtain ⟨nu, hnu, vn⟩ := ((grep_sigma hσ (snd (TFK (R := R) F) A.A)).pow 4).inv.out hL
    ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ ι[A.A]).left] ![((4 : ℕ) : ℤ), -((4 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (snd (TFK (R := R) F) A.A).left ^ ((4 : ℕ) : ℤ) * h ((snd (TFK (R := R) F) A.A)⁻¹).left ^ (-((4 : ℕ) : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  have vn' : ∀ y J, Good A.L y J → ∀ m, negVal (L := A.L) (k := ((4 : ℕ) : ℤ)) nu y J m = (val σ m.left y J ^ 4)⁻¹ :=
    fun y J hJ m => (vn _ _ y J hJ).trans (by beta_reduce; rw [lift_snd])
  obtain ⟨a, ha⟩ := exists_symConst hG A.isAb hL θ₀ (nu := nu) hnu
  obtain ⟨b, hb⟩ : ∃ b : Γ((TFK (R := R) F).left, ⊤)ˣ, a = b ^ 2 := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (e a.val) two_pos
    have e₁ : (e.symm r) ^ 2 = a.val := by rw [← map_pow, hr, RingEquiv.symm_apply_apply]
    have u : IsUnit (e.symm r) := (isUnit_pow_iff two_ne_zero).1 (e₁ ▸ a.isUnit)
    exact ⟨u.unit, Units.ext e₁.symm⟩
  obtain ⟨θ, hpt, hv⟩ := exists_scale hL θ₀ b⁻¹
  have hθ : θ.pt = x := hpt.trans h₀
  have hs : LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L) := corr_of_val hL fun y J hJ => by
    have e₁ := (val_symGen θ₀ nu h₀ hJ (snd _ _)).symm.trans (ha _ y J hJ)
    rw [val_one, id_eq_lift, val_symGen θ nu hθ hJ, hv y J hJ, hv y J hJ, map_inv]
    rw [hb, map_pow] at e₁
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ ⊢
    linear_combination (norm := module) e₁
  obtain ⟨K, _, φ, ε, s, hs', p, vs⟩ := grep_sigma hσ (x ^ 2)
  obtain ⟨c, hc⟩ := H1.exists_const A.L hL (𝟙 _) (fun v => ⟨v, by simp⟩) s hs' (fun U _ h => (p U h).trans (by
    have e : (x ^ 2)⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hx
    beta_reduce
    rw [e, mul_inv_cancel]))
  have ec : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, hθ, ⟨nu, hnu, hs⟩, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun z J hJ => ?_, ?_⟩
  · have e₁ := vs _ (𝟙 _) z J hJ
    have e₂ := hc _ (𝟙 _) z J hJ
    beta_reduce at e₁
    rw [Category.id_comp, Over.id_left] at e₁
    rw [Category.id_comp] at e₂
    exact (congrArg Units.val e₁).symm.trans (e₂.trans (congrArg (gs _ z ⊤) ec.symm))
  · rintro ψ m hm hψ rfl α hα t t₁ t₂ t₃ h₁ h₂ h₃ j
    rw [ec]
    refine eq_liftFun_mul hL t₁ t₃ c (fun y J hJ => ?_) j
    subst hθ
    have key := square_val hG A.isAb hL hσ hσ₁ θ hx nu vn' hs hα y J hJ
    have e₁ := vs _ (fst _ A.A) y J hJ
    have e₂ := hc _ (fst _ A.A).left y J hJ
    beta_reduce at e₁
    rw [MonObj.comp_pow] at e₁
    rw [Category.comp_id, e₁] at e₂
    have hX : (fst (TFK (R := R) F) A.A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have eψ : lift (fst (TFK (R := R) F) A.A) ((fst _ _ ≫ θ.pt) * ((fst _ _ ≫ θ.pt) * snd _ _)) ≫ ψ =
        lift (fst _ _) (snd _ _) ≫ ψ := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hψ, lift_fst, lift_fst]
      · rw [Category.assoc, Category.assoc, hm, MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd,
          ← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
    rw [← e₂, id_eq_lift, ThetaLin.sval_of_isTwistPull A.A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₂ _ y hJ,
      ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ]
    simp only [← Over.comp_left]
    rw [lift_translT, lift_translT, eψ]
    have alg : ∀ {M : Type} [CommMonoid M] (a b c d e : Mˣ) (w : M), a * (b * c) = d * e →
        a.val * (b.val * (c.val * w)) = d.val * (e.val * w) := fun a b c d e w h => by
      have h' := congrArg (fun u => Units.val u * w) h
      simpa only [Units.val_mul, _root_.mul_assoc] using h'
    exact alg _ _ _ _ _ _ key

end GlobalTheory.ThetaSquare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAddEpsMulOnDualNumberThickening
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EpsThick

theorem existsUnique_add_eps_mul_of_field : ∀ (k : Type) [Field k] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp k) (π : Y' ⟶ Sp (DualNumber k)) (ρ : Y' ⟶ Y), IsPullback ρ π q (spMap (algebraMap k (DualNumber k))) → ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro k _ Y Y' q π ρ H O F
  obtain ⟨ab, hab⟩ := comb_surjective H O F
  exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualNumberThickeningOpenDecompStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dualNumberThickening_open_decomp : ∀ (R : Type) [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R)) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))) → ∀ (O : Z.Opens) (F : Γ(P, p₂ ⁻¹ᵁ O)), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 := by
  first | exact @GlobalTheory.SpThickening.existsUnique_decomp | exact GlobalTheory.SpThickening.existsUnique_decomp | (intros; apply GlobalTheory.SpThickening.existsUnique_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTau

theorem commGroup_seven_term_product_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * b * c * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  calc _ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) * (b * b⁻¹) * (c * c⁻¹) := by ac_rfl
    _ = _ := by simp

set_option maxHeartbeats 1000000 in

theorem exists_isUnitTau : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → (∀ i y z, gam i y z = gam i z y) → (∀ i, t i ≠ 0) → ∀ y z, ∃ τ₀, IsUnitTau Q t gam y z τ₀ := by
  intro R _ _ Q m t gam hM hsym ht y z
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM (y + z)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM y
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM z
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)

  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hp1.1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hp2.1))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hp3.1)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen Q.P.isLB hF T hT
  refine ⟨τ₀, hτ, ?_⟩

  obtain ⟨-, hn1, e1, he1, hv1⟩ := hp1
  obtain ⟨-, hn2, e2, he2, hv2⟩ := hp2
  obtain ⟨-, hn3, e3, he3, hv3⟩ := hp3
  have hne : ∀ i, algebraMap R (FractionRing R) (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht i)
  let e' : (FractionRing R)ˣ := ∏ i, Units.mk0 _ (hne i) ^ gam i y z
  have he' : (e' : FractionRing R) = ∏ i, algebraMap R _ (t i) ^ gam i y z := by
    simp [e', Units.coe_prod]
  have hexp : ∀ i, (n1 i : ℤ) = gam i y z + n2 i + n3 i := by
    intro i
    have a := hn1 i
    have b := hn2 i
    have c := hn3 i
    have s := hsym i y z
    simp only [map_add, LinearMap.add_apply] at a
    linarith
  have hee : e1 = e' * e2 * e3 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he2, he3, he']
    simp only [map_prod, map_pow]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i), hexp i]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  refine ⟨e', he', fun zz J hJ => ?_⟩
  rw [hv _ _ zz J hJ]
  simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
  rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, hee, hu, hu, map_mul, map_mul, Category.id_comp]
  exact commGroup_seven_term_product_rearrange _ _ _ _ _ _ _

end GlobalTheory.UnitTau
end
end

