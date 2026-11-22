import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBounds
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

theorem valuation_chain_ratio_bounds (k : Type) [Field k] [ValuativeRel k] (m : ℕ) (r1 r2 : Fin m → kˣ) :
    ∃ R1 R2 : kˣ, 1 ≤ valuation k (R1 : k) ∧ valuation k (R2 : k) ≤ 1 ∧
      ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 →
        (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧
          valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) →
        ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  induction m with
  | zero =>
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro t ht _ i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst hi
    rw [ht]; simp
  | succ m ih =>
    obtain ⟨R1', R2', h1', h2', hR⟩ := ih (fun j => r1 j.succ) (fun j => r2 j.succ)
    set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def
    set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def
    have ha1 : 1 ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have har : valuation k (r1 0 : k) ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    have hb1 : valuation k (b : k) ≤ 1 := by
      rw [hb_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have hbr : valuation k (b : k) ≤ valuation k (r2 0 : k) := by
      rw [hb_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    refine ⟨R1' * a, R2' * b, ?_, ?_, ?_⟩
    · simp only [Units.val_mul, map_mul]
      exact one_le_mul h1' ha1
    · simp only [Units.val_mul, map_mul]
      exact mul_le_one' h2' hb1
    intro t ht hrat
    have hT := hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by
      have := hrat i.succ
      rw [← Fin.succ_castSucc] at this; exact this)
    have hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k) := by
      simp only [Units.val_mul, map_mul]; exact le_mul_of_one_le_right' ha1
    have hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k) := by
      simp only [Units.val_mul, map_mul]; exact mul_le_of_le_one_right' hb1
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hrat 0
      have ht1 := hT 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1
      have hne : ((t 1 : kˣ) : k) ≠ 0 := (t 1).ne_zero
      have hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1 := by field_simp
      rw [hsplit, map_mul]
      constructor
      · simp only [Units.val_mul, map_mul]
        calc valuation k (R2' : k) * valuation k (b : k)
            = valuation k (b : k) * valuation k (R2' : k) := mul_comm _ _
          _ ≤ valuation k (r2 0 : k) * valuation k (t 1 : k) := mul_le_mul' hbr ht1.1
          _ ≤ _ := mul_le_mul' h0.1 le_rfl
      · simp only [Units.val_mul, map_mul]
        calc valuation k ((t 0 : k) / t 1) * valuation k (t 1 : k)
            ≤ valuation k (r1 0 : k) * valuation k (R1' : k) := mul_le_mul' h0.2 ht1.2
          _ ≤ valuation k (a : k) * valuation k (R1' : k) := mul_le_mul' har le_rfl
          _ = _ := mul_comm _ _
    · have := hT j
      exact ⟨hR2le.trans this.1, this.2.trans hR1le⟩

theorem chain_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  intro k _ _ _ _ m r1 r2
  obtain ⟨R1, R2, -, -, h⟩ := valuation_chain_ratio_bounds k m r1 r2
  exact ⟨R1, R2, h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwExtend
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.SJ.Place

theorem exists_tw_extend {H K X : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (V : Submodule ℂ X) (φ : V →ₗ⋆[ℂ] K) (z : ℂ) (s : Bool) :
    ∃ sE : Tw s H →ₗ⋆[ℂ] Tw s K, ∀ (x : Tw s H) (hx : e (Tw.out x) ∈ V), sE x = Tw.mk s (z • φ ⟨e (Tw.out x), hx⟩) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V.comap e) (e.restrict (p := V.comap e) (q := V) fun _ h => h)
  refine ⟨{ toFun := fun x => Tw.mk s (z • φ (g (Tw.out x))), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    show z • φ (g (Tw.out x + Tw.out y)) = z • φ (g (Tw.out x)) + z • φ (g (Tw.out y))
    rw [map_add, map_add, smul_add]
  · intro a x
    show z • φ (g (cj s a • Tw.out x)) = cj s (starRingEnd ℂ a) • z • φ (g (Tw.out x))
    rw [map_smul, map_smulₛₗ, cj_conj, smul_comm]
  · intro x hx
    have := LinearMap.congr_fun hg ⟨Tw.out x, hx⟩
    show Tw.mk s (z • φ (g (Tw.out x))) = _
    rw [show g (Tw.out x) = ⟨e (Tw.out x), hx⟩ from this]

theorem scale_norm {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {c n a : ℝ} (hc : 0 < c) (hn : 0 < n) (y : K)
    (h : ‖y‖ ^ 2 = c * a) : n * ‖((1 : ℂ) * (((Real.sqrt (c * n))⁻¹ : ℝ) : ℂ)) • y‖ ^ 2 = a := by
  have hcn : 0 < c * n := mul_pos hc hn
  rw [one_mul, norm_smul, Complex.norm_real, mul_pow, h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hcn.le]
  field_simp

theorem sEEofTT_spec {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0)))
    (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) (h : EvalTieT M μ 𝓕 E X G ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E X G ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re ∧
      ((sEEofTT M μ 𝓕 E X G ι t c T : HHX X) : L2X X) ∈ goodSub X G := by
  have e : sEEofTT M μ 𝓕 E X G ι t c = (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap := by
    unfold sEEofTT
    exact dif_pos h
  have e' : sEEofTT M μ 𝓕 E X G ι t c T = conjHH X G (h.choose_spec.2.choose T) := by
    rw [e]
    rfl
  rw [e']
  refine ⟨?_, (mem_EEC X G _).1 (h.choose_spec.2.choose T).2⟩
  rw [(conjHH X G).norm_map]
  exact (h.choose_spec.2.choose_spec T).2

theorem exists_placement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (ι : GA D (Yc D 0) ≃* St.B.I.GA) (t : GA D (Yc D 0)) (c : ℝ) (s : Bool), R.models_HE → 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c → ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX St)), 0 < κ ∧ ∀ (x : Tw s R.HE.H) (hx : R.HE.e (Tw.out x) ∈ R.EEat (R.levR F true)), sE x = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F true * ‖sE x‖ ^ 2 = ‖x‖ ^ 2 ∧ ((Tw.out (sE x) : HHX St) : L2X St) ∈ goodSub St Gd := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F St Gd ι t c s hE hc h
  have hn : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  obtain ⟨sE, hs⟩ := exists_tw_extend R.HE.e (R.EEat (R.levR F true))
    (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c)
    ((1 : ℂ) * (((Real.sqrt (c * RealDat.nP F true))⁻¹ : ℝ) : ℂ)) s
  refine ⟨(Real.sqrt (c * RealDat.nP F true))⁻¹, sE, inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hn)), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sEEofTT_spec (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c h ⟨R.HE.e (Tw.out x), hx⟩
  refine ⟨hs x hx, ?_, ?_⟩
  · rw [hs x hx]
    have hip : (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2 := by
      rw [← hE.2.2]
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Tw.out x)).symm
    have key := scale_norm (K := HHX St) hc hn
      (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) (h1.trans (congrArg (c * ·) hip))
    exact key
  · rw [hs x hx]
    exact (goodSub St Gd).smul_mem _ h2

end GlobalTheory.Mem.SJ.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_infSpan (φ : UA E n → ℂ) {x : UA E n} (hx : x ∈ infU E n) {ψ : UA E n → ℂ} (hψ : ψ ∈ infSpan φ) :
    RU E n x ψ ∈ infSpan φ := by
  have : infSpan φ ≤ (infSpan φ).comap (RU E n x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show RU E n x (RU E n k φ) ∈ infSpan φ
    rw [RU_RU]
    exact Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩
  exact this hψ

theorem mem_infU_of_mem_embU {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) : x ∈ infU E n :=
  (Subgroup.mem_inf.1 hx).1

theorem exists_hasWeightAt (U : AutSub E n) (τ : E →+* ℂ) : ∃ lam, HasWeightAt U.V τ lam := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot
  let j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hj : ∀ u, j u ∈ infU E n := fun u => mem_infU_of_mem_embU (e.symm u).2
  let S := infSpan φ
  have hφS : φ ∈ S := by
    have : RU E n (1 : infU E n) φ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using this
  have hS : S ≤ U.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)
  haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin
  haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S :=
    sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)
  have hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v := fun _ _ => rfl
  have hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v) := by
    let P : Submodule ℂ (Module.Dual ℂ S) :=
      { carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)}
        add_mem' := fun ha hb v => (ha v).add (hb v)
        zero_mem' := fun _ => continuous_const
        smul_mem' := fun c _ ha v => (ha v).const_smul c }
    have hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P := fun g v => by
      have hv : Continuous (v : UA E n → ℂ) := (U.isAut.aut _ (hS v.2)).cont
      have : Continuous fun u => (j u : UA E n) := continuous_subtype_val.comp e.symm.continuous
      exact hv.comp ((continuous_const_mul g).comp this)
    have h1 : P.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))
    have hP : P = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]
    intro l v
    have : l ∈ P := hP ▸ Submodule.mem_top
    exact this v
  obtain ⟨lam, f, hf⟩ := GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep n S ρ hcont
  refine ⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_,
    fun v => hS (f v).2, fun x v => ?_⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)
    simpa using LinearMap.congr_fun h0 v
  · have h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x) := (he x).symm
    rw [h1]
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ f (e x) v
    change (f (smallRep (unitaryIncl n) lam (e x) v)).1 = _
    rw [h2, hρ]
    change RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _
    rw [e.symm_apply_apply]
    rfl

theorem hasWeightAt_unique (U : AutSub E n) (τ : E →+* ℂ) {lam lam' : DomWeight n} (h : HasWeightAt U.V τ lam)
    (h' : HasWeightAt U.V τ lam') : lam = lam' := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E n τ
  let s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ mu, HasWeightAt U.V τ mu →
      ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro mu ⟨-, F, hF0, hFm, hFi⟩
    refine ⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)
      have : unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u) := by
        have h3 := he (e.symm u)
        rw [e.apply_symm_apply] at h3
        exact h3
      rw [this, hFi]
      rfl
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  obtain ⟨f, hf⟩ := mk lam h
  obtain ⟨f', hf'⟩ := mk lam' h'
  have hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨ee⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam)
    (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'
  by_contra hne
  have h0 := intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ n lam)
  exact hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))

theorem AU.existsUnique_hasWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  intro E _ _ _ n π τ
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨lam, h⟩ := exists_hasWeightAt U τ
  exact ⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilSurj

open GlobalTheory.WeilRestrict Polynomial

theorem card_le_of_forall_pow_eq {F : Type*} [Field F] [Finite F] {m : ℕ} (hm : 1 < m)
    (h : ∀ x : F, x ^ m = x) : Nat.card F ≤ m := by
  classical
  haveI := Fintype.ofFinite F
  have hdeg : (X : F[X]).natDegree < (X ^ m : F[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]; exact hm
  have hp : (X ^ m - X : F[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow, natDegree_zero] at this
    omega
  have hsub : (Finset.univ : Finset F) ⊆ (X ^ m - X : F[X]).roots.toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    simp [h x]
  calc Nat.card F = (Finset.univ : Finset F).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = m := by rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow]

theorem exists_weil_of_fixes : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w W h h' σ hσ
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  have hq1 : 1 < normV w := one_lt_normV w
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := one_lt_normV W
      rw [hf, h0, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h0
  have hφdeg : deg (resWeil h h' (frob h')) = f := by
    have h1 : ActsAs A (normV w ^ f) (frob h' : G K Ω) 1 0 := by
      rw [← hf]; exact actsAs_one_iff.mpr isFrob_frob
    have h2 := actsAs_resG (K := E) h1
    have := deg_eq (σ := resWeil h h' (frob h')) h2
    simpa using this
  obtain ⟨k, r, hr0, hrf, hdr⟩ : ∃ k r : ℤ, 0 ≤ r ∧ r < f ∧ r + f * k = deg σ :=
    ⟨deg σ / f, deg σ % f, Int.emod_nonneg _ (by exact_mod_cast hf0.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hf0), Int.emod_add_mul_ediv _ _⟩
  set σ' : Weil h := σ * (resWeil h h' (frob h' ^ k))⁻¹ with hσ'
  have hdeg' : deg σ' = r := by
    rw [hσ', deg_mul, deg_inv, map_zpow, deg_zpow, hφdeg]
    linear_combination -hdr
  have hfix' : ∀ x : K, (σ' : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
    intro x
    rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, ← map_inv, resWeil_apply, AlgEquiv.commutes, hσ]
  have hr : r = 0 := by
    by_contra hne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne)
    set n := r.toNat with hn'
    have hn : (n : ℤ) = r := Int.toNat_of_nonneg hr0
    have hact := actsAs_of_deg (σ := σ') (a := n) (b := 0) (by rw [hdeg', hn]; simp)
    have hmem : ∀ x : 𝓞 K, x ^ (normV w ^ n) - x ∈ W.asIdeal := by
      intro x
      rw [← h' _]
      have hx : A.valuation (algebraMap K Ω x) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (map_isIntegral_int (algebraMap K Ω) x.isIntegral_coe))
      have := hact.2 _ hx
      rw [hfix', pow_zero, pow_one, Valuation.map_sub_swap] at this
      have e : algebraMap K Ω ((x ^ (normV w ^ n) - x : 𝓞 K) : K) =
          (algebraMap K Ω x) ^ (normV w ^ n) - algebraMap K Ω x := by simp
      rw [e]; exact this
    haveI : W.asIdeal.IsMaximal := W.isMaximal
    letI : Field (𝓞 K ⧸ W.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 K ⧸ W.asIdeal) := W.asIdeal.finiteQuotientOfFreeOfNeBot W.ne_bot
    have hall : ∀ y : 𝓞 K ⧸ W.asIdeal, y ^ (normV w ^ n) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem x
    have hn0 : n ≠ 0 := by omega
    have hcard := card_le_of_forall_pow_eq (one_lt_pow₀ hq1 hn0) hall
    have hQ : Nat.card (𝓞 K ⧸ W.asIdeal) = normV w ^ f := hf
    rw [hQ] at hcard
    have : normV w ^ n < normV w ^ f := Nat.pow_lt_pow_right hq1 (by omega)
    omega
  have hine : (σ' : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp (by rw [hdeg', hr])
  let τ0 : G K Ω := { (σ' : G E Ω).toRingEquiv with commutes' := fun x => hfix' x }
  have hτ0 : τ0 ∈ Ine (F := K) A := hine
  refine ⟨ineIncl h' ⟨τ0, hτ0⟩ * frob h' ^ k, fun z => ?_⟩
  have key : (((resWeil h h' (frob h' ^ k))⁻¹ : Weil h) : G E Ω)
      (((frob h' ^ k : Weil h') : G K Ω) z) = z := by
    rw [← map_inv, resWeil_apply, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, AlgEquiv.one_apply]
  show (σ : G E Ω) z = (σ' : G E Ω) (((frob h' ^ k : Weil h') : G K Ω) z)
  rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, key]

end GlobalTheory.WeilSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.NormalPole

theorem exists_height_one {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (f : K) (Q : Ideal R)
    (hQ : ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ Q) [Q.IsPrime] :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ Q ∧ p.height = 1 ∧
      ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ p := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R K s * (algebraMap R K b / algebraMap R K c) =
      algebraMap R K e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff,
      mul_comm e]
  have hdQ : d ≤ Q := fun s hs => by
    obtain ⟨e, he⟩ := (reg s).2 hs
    exact hQ s e he
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  exact ⟨p, hpp, hpQ, h1, fun s e he => hp.1.2 ((reg s).1 ⟨e, he⟩)⟩

theorem mem_range_iff {R B K : Type} [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra R K]
    [Algebra B K] [IsScalarTower R B K] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime B p] (f : K) :
    (∃ a : B, algebraMap B K a = f) ↔
      ∃ s c : R, algebraMap R K s * f = algebraMap R K c ∧ s ∉ p := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨s, c, ?_, s.2⟩
    rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K c, ← map_mul,
      mul_comm, e]
  · rintro ⟨s, c, e, hs⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
    refine ⟨↑u⁻¹ * algebraMap R B c, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← e, IsScalarTower.algebraMap_apply R B K s]
    have hu' : algebraMap R B s = u := hu.symm
    rw [hu', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]

theorem exists_zeroAt_inv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (x : X) (f : X.functionField), ¬ RegAt x f → ∃ z : X, z ⤳ x ∧ ZeroAt z f⁻¹ := by
  intro X _ _ hN x f hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks (fun y => (hN y).2) hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  refine ⟨z, hzx, zeroAt_iff.2 ⟨?_, fun h => hfz ?_⟩⟩
  · exact (ValuationRing.isInteger_or_isInteger (X.presheaf.stalk (z : X)) f).resolve_left hfz
  · simpa using h.inv.regAt

end GlobalTheory.NormalPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS g : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT h : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => BS τ * g τ) (fun τ => BT τ * h τ) f P = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) P) := by
  first | exact @GlobalTheory.FockBaseChange.pureTensorO_subst | exact GlobalTheory.FockBaseChange.pureTensorO_subst | (intros; apply GlobalTheory.FockBaseChange.pureTensorO_subst <;> assumption)
end

