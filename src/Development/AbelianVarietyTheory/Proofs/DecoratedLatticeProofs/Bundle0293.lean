import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CellProd

theorem prod_ofFn_mul {M : Type} [Monoid M] : ∀ {n : ℕ} (r u : Fin n → M), (∀ i i', i ≠ i' → Commute (u i) (r i')) →
    (List.ofFn fun i => r i * u i).prod = (List.ofFn r).prod * (List.ofFn u).prod
  | 0, _, _, _ => by simp
  | n + 1, r, u, h => by
    have ih := prod_ofFn_mul (fun i => r i.succ) (fun i => u i.succ)
      (fun i i' hi => h _ _ fun e => hi (Fin.succ_injective _ e))
    have hc : Commute (u 0) (List.ofFn fun i : Fin n => r i.succ).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, mul_assoc, mul_assoc, ← mul_assoc (u 0), hc.eq, mul_assoc]

theorem prod_ofFn_single {M : Type} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ i', i' ≠ i → f i' = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero i)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_single (fun i => f i.succ) i fun i' hi => h _ fun e => hi (Fin.succ_injective _ e)

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem idAt_le {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mem_idAt (q : SplitPt D k) {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)

theorem idem_mul_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : (q.e + cA D q.e) * a = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  rw [hs]
  exact (placeIdem_acts D q.v ε hε).2 a (idAt_le (fun v (e : v = q'.v) => e ▸ hv) (mem_idAt q' h))

theorem pr_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : q.pr a = 0 := by
  have h0 := idem_mul_eq_zero q q' hv h
  obtain ⟨h1, h2, -⟩ := q.split
  have : q.e * a = 0 := by
    have := congrArg (q.e * ·) h0
    simpa only [← mul_assoc, mul_add, h1, h2, add_zero, mul_zero] using this
  rw [← q.pr_sec (q.pr a), q.sec_pr, this, map_zero]

theorem mem_grpAt (q : SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt q.e V g) {P : Pl D → Prop} (hP : P q.v) :
    g ∈ grpAt V P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idAt D P)) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]
  exact idAt_le (fun v (e : v = q.v) => e ▸ hP) (mem_idAt q (hg i j))

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp [Formalism.L2.Theta.mt]

theorem sub_mul_sub (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) :
    (mt V g - 1) * (mt V h - 1) = 0 ∧ (mt V h - 1) * (mt V g - 1) = 0 := by
  have key : ∀ a b c d, (mt V g - 1) a b * (mt V h - 1) c d = 0 := fun a b c d => by
    rw [← hg a b, mul_comm (q.e + _), mul_assoc, idem_mul_eq_zero q q' hv (hh c d), mul_zero]
  constructor
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => key _ _ _ _
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact key _ _ _ _

theorem commute_of_suppAt (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) : Commute g h := by
  obtain ⟨h1, h2⟩ := sub_mul_sub q q' hv hg hh
  have : mt V (g * h) = mt V (h * g) := by
    rw [mt_mul', mt_mul', ← sub_eq_zero]
    have e : mt V g * mt V h - mt V h * mt V g = (mt V g - 1) * (mt V h - 1) - (mt V h - 1) * (mt V g - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  exact Subtype.ext (Units.ext this)

theorem map_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q'.e V g) : (mt V g).map q.pr = 1 := by
  ext i j
  have := pr_eq_zero q q' hv (hg i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, ← Matrix.map_one q.pr (map_zero _) (map_one _), Matrix.map_apply]

def matAt (q : SplitPt D k) (V : HSp D) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) k :=
  (q.pr.mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (matHom V)

end GlobalTheory.SeeSaw.CellProd

open GlobalTheory.SeeSaw.CellProd in

theorem GlobalTheory.SeeSaw.prod_local_cells : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  intro D c v n G hG j' hj R b hb xs H
  choose r hr hrs u uk hu huk hx using H
  have hne : ∀ i i', i ≠ i' → (G i).q.v ≠ (G i').q.v := fun i i' h e => h (hG.inj e)
  have hP : ∀ i, (G i).q.v ∈ v.gP := fun i => (hG.places _).2 ⟨i, rfl⟩
  have hus : ∀ i, SuppAt (G i).q.e (c.V j') (u i) := fun i => (hu i).1
  refine ⟨(List.ofFn r).prod, R.list_prod_mem ?_, Subgroup.list_prod_mem _ ?_, (List.ofFn u).prod,
    (hG.lev j' hj _).2 ⟨Subgroup.list_prod_mem _ ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hr i
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact mem_grpAt (G i).q (hrs i) (hP i)
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact mem_grpAt (G i).q (hus i) (hP i)
  · intro i a ha y hy
    obtain rfl : a = b i := by have := hb i; omega
    have e : matAt (G i).q (c.V j') (List.ofFn u).prod = matAt (G i).q (c.V j') (u i) := by
      rw [map_list_prod, List.map_ofFn]
      exact prod_ofFn_single _ i fun i' hi => map_eq_one (G i).q (G i').q (hne _ _ hi) (hus i')
    have e2 : ((G i).FY j' (b i) ha).β * y.val * ((G i).FY j' (b i) ha).γ =
        ((G i).FY j' (b i) ha).β * (uk i).val * ((G i).FY j' (b i) ha).γ := hy.symm.trans (e.trans (hu i).2)
    have e3 := congrArg (fun x => ((G i).FY j' (b i) ha).γ * x * ((G i).FY j' (b i) ha).β) e2
    simp only [← Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.one_mul] at e3
    simp only [Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.mul_one] at e3
    rw [Units.ext e3]
    exact huk i
  · rw [show xs = fun i => r i * u i from funext hx]
    exact prod_ofFn_mul r u fun i i' h => commute_of_suppAt (G i).q (G i').q (hne _ _ h.symm) (hus i) (hrs i')

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.ReadLaws

theorem isInv_of_isUni {ι : Type} {n : ℕ} {u : ι → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) : IsInv u := by
  intro τ
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp (hu τ))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

def trFr {ι : Type} {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : IsInv g)
    (y : Frames G) : Frames G :=
  ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩

theorem continuous_valC {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {lam : ι → DomWeight n}
    {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) {X : Type} [TopologicalSpace X] {f : X → ι → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hi : ∀ x τ, IsUnit (f x τ).det) : Continuous fun x => Φ ⟨f x, hi x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  have e : (fun x => fnOf G (shiftOf lam) 1 P (⟨f x, hi x⟩ : Frames G)) =
      fun x => (∏ τ, (f x τ).det ^ shiftOf lam τ) * GlobalTheory.KJInf.evalAt (f x) P :=
    funext fun x => GlobalTheory.KJInf.ValPol.fnOf_one_apply _ P _
  rw [e]
  simp only [GlobalTheory.KJInf.ValPol.evalAt_eq]
  refine Continuous.mul (continuous_finset_prod _ fun τ _ => ?_) ?_
  · exact (((continuous_apply τ).comp hf).matrix_det).zpow₀ _ fun x => Or.inl (hi x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun v => ((continuous_apply v.1).comp hf).matrix_elem v.2.1 v.2.2)

end GlobalTheory.SeeSaw.ReadLaws

open GlobalTheory.SeeSaw.ReadLaws in

theorem GlobalTheory.SeeSaw.scalarForm_laws : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  intro D c t ρ A _hc hρ hA j hj ψ hψ β
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.X j)
  have hr := hρ.uni j hj
  have hinv : ∀ k : GinfC (c.X j), IsInv (ρ.r j hj k.1) := fun k => isInv_of_isUni (hr.uni k)
  have hR := hA.reps j hj β
  have hrd : ∀ y γ, γ ∈ GQ (c.X j) → ∀ a k (hk : k ∈ GinfC (c.X j)) (κ : A.U j β),
      t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) =
        (A.chi j β κ : ℂ) * A.val j β ψ a (trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y)) :=
    fun y γ hγ a k hk κ => hA.rd j hj ψ hψ β y γ hγ a k hk κ _ (fun τ => rfl)
  have hcomm : ∀ k ∈ GinfC (c.X j), ∀ κ ∈ GfC (c.X j), k * κ = κ * k := fun k hk κ hκ =>
    (GlobalTheory.AutMult.commute_inf_fin (V := c.X j) ⟨k, hk⟩ ⟨κ, hκ⟩).eq
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ' hγ' g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ' * (γ * (A.h j β a * k) * κ) = (γ' * γ) * (A.h j β a * k) * (⟨κ, hκ⟩ : A.U j β).1 := by
      simp only [mul_assoc]
    rw [e, hrd y _ (mul_mem hγ' hγ) a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩]
  · rw [continuous_iff_continuousAt]
    intro g0
    obtain ⟨γ, hγ, a, k0, hk0, κ0, hκ0, rfl⟩ := hR.dec g0
    set q : GA D (c.X j) → GA D (c.X j) := fun g => (γ * A.h j β a)⁻¹ * g with hqdef
    have hq : Continuous q := continuous_const.mul continuous_id
    set W : Set (GA D (c.X j)) :=
      {g | ((GlobalTheory.AutMult.toFin (c.X j) (q g) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β} with hWdef
    have hW : IsOpen W := hR.opn.preimage ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp hq)
    have h0 : GlobalTheory.AutMult.toFin (c.X j) (q (γ * (A.h j β a * k0) * κ0)) = ⟨κ0, hR.le hκ0⟩ := by
      have e : q (γ * (A.h j β a * k0) * κ0) =
          ((⟨k0, hk0⟩ : GinfC (c.X j)) : GA D (c.X j)) * ((⟨κ0, hR.le hκ0⟩ : GfC (c.X j)) : GA D (c.X j)) := by
        show (γ * A.h j β a)⁻¹ * (γ * (A.h j β a * k0) * κ0) = k0 * κ0
        group
      rw [e, map_mul, GlobalTheory.AutMult.toFin_coe_inf, GlobalTheory.AutMult.toFin_coe, one_mul]
    have hg0 : γ * (A.h j β a * k0) * κ0 ∈ W := by
      show ((GlobalTheory.AutMult.toFin (c.X j) (q _) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β
      rw [h0]
      exact hκ0
    refine ContinuousOn.continuousAt ?_ (hW.mem_nhds hg0)
    rw [continuousOn_iff_continuous_restrict]
    have hU : ∀ g : W, ((GlobalTheory.AutMult.toFin (c.X j) (q g.1) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β := fun g => g.2
    show Continuous fun g : W => t.rd j β ψ y g.1
    have key : (fun g : W => t.rd j β ψ y g.1) = fun g : W => (A.chi j β ⟨_, hU g⟩ : ℂ) *
        A.val j β ψ a (trFr (ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) (hinv _) (ρ.fr j y)) := by
      funext g
      have e : g.1 = γ * (A.h j β a * (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) * (⟨_, hU g⟩ : A.U j β).1 := by
        have h1 := GlobalTheory.AutMult.toInf_mul_toFin (q g.1)
        calc g.1 = (γ * A.h j β a) * q g.1 := by
              show g.1 = (γ * A.h j β a) * ((γ * A.h j β a)⁻¹ * g.1)
              group
          _ = _ := by
              conv_lhs => rw [← h1]
              simp only [mul_assoc]
      exact (congrArg (t.rd j β ψ y) e).trans (hrd y γ hγ a _ (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).2 _)
    rw [key]
    refine Continuous.mul ?_ ?_
    · have hc : Continuous fun g : W => (⟨_, hU g⟩ : A.U j β) :=
        Continuous.subtype_mk (continuous_subtype_val.comp
          ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp (hq.comp continuous_subtype_val))) _
      exact (hA.chi j hj β).comp hc
    · have hk : Continuous fun g : W => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 :=
        hr.cont.comp ((GlobalTheory.AutMult.continuous_toInf (c.X j)).comp (hq.comp continuous_subtype_val))
      exact continuous_valC (f := fun g : W => fun τ => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 τ * (ρ.fr j y).1 τ)
        (hA.valC j hj ψ hψ β a) (continuous_pi fun τ => ((continuous_apply τ).comp hk).matrix_mul continuous_const) _
  · intro y g κ'
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * κ'.1 = γ * (A.h j β a * k) * ((⟨κ, hκ⟩ : A.U j β) * κ').1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, hrd y γ hγ a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩, map_mul, Units.val_mul]
    ring
  · intro y y' g k' hk' htr
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * k' = γ * (A.h j β a * (k * k')) * (⟨κ, hκ⟩ : A.U j β).1 := by
      rw [mul_assoc _ κ k', ← hcomm k' hk' κ (hR.le hκ)]
      simp only [mul_assoc]
    rw [e, hrd y γ hγ a _ (mul_mem hk hk'), hrd y' γ hγ a k hk ⟨κ, hκ⟩]
    have hY : trFr (ρ.r j hj (k * k')) (hinv ⟨k * k', mul_mem hk hk'⟩) (ρ.fr j y) =
        trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y') := by
      apply Subtype.ext
      funext τ
      have hm : ρ.r j hj (k * k') τ = ρ.r j hj k τ * ρ.r j hj k' τ := hr.mul ⟨k, hk⟩ ⟨k', hk'⟩ τ
      show ρ.r j hj (k * k') τ * (ρ.fr j y).1 τ = ρ.r j hj k τ * (ρ.fr j y').1 τ
      rw [htr τ, hm, Matrix.mul_assoc]
    rw [hY]
  · intro g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have hv := hA.valC j hj ψ hψ β a
    refine (GlobalTheory.KJInf.valC_poly _ _ _ _).2.2.1 ((A.chi j β ⟨κ, hκ⟩ : ℂ) • A.val j β ψ a) (Submodule.smul_mem _ _ hv)
      (ρ.r j hj k) _ ?_ (hinv ⟨k, hk⟩)
    intro z z' hz
    rw [hA.rd j hj ψ hψ β _ γ hγ a k hk ⟨κ, hκ⟩ z' (by rwa [Equiv.apply_symm_apply])]
    rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramePeriod

variable {D : D7}

theorem setIntegral_mul_right_N {ρ : ℕ} (B : BesLev D ρ) (G : flagN B.d → ℂ)
    (hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n, G (γ * n) = G n) (y : flagN B.d) :
    ∫ n in B.vN.𝓝, G (n * y) ∂B.vN.ν = ∫ n in B.vN.𝓝, G n ∂B.vN.ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  haveI : DiscreteTopology (NFlagQ B.V B.d.e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B.V B.d.e => (⟨γ.1.1, γ.2⟩ : GQ B.V)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B.V => (x : GA D B.V)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  have hcov' : ∀ x : flagN B.d, ∃ s ∈ NFlagQ B.V B.d.e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : flagN B.d, B.vN.ν.map (· * a) = B.vN.ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vN.ν (NFlagQ B.V B.d.e) hK hcov' a
  have hmp : MeasurePreserving (· * y) B.vN.ν B.vN.ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) B.vN.ν B.vN.ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) G B.vN.𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B.V B.d.e) ((· * y⁻¹) ⁻¹' B.vN.𝓝) B.vN.ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem inner_N {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n ∂B.vN.ν =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨-, -, hconj, -, -⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hx' : GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹ ∈ flagN B.d := hconj x hx h
  have hpy : psiBes ψ B.d 1 (vecB B.o B.ζ) (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x := hψconj x h
  have hn1 : psiBes ψ B.d 1 (vecB B.o B.ζ) x * star (psiBes ψ B.d 1 (vecB B.o B.ζ) x) = 1 := by
    have hnorm : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) x‖ = 1 := by simp only [psiBes, psiE]; exact hψ.2.1 _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  let y : flagN B.d := ⟨_, hx'⟩
  have hpt : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * besFun ψ 1 B.d B.o B.ζ φ f h (n * y) := fun n => by
    simp only [besFun, rTrans, Subgroup.coe_mul, y]
    rw [psiBes_mul B.d ψ 1 _ n.2 hx', hpy, star_mul]
    have e1 : (n : GA D B.V) * (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) *
        GlobalTheory.MixPer.embA B.d B.o h = (n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x := by group
    rw [e1]
    linear_combination (-(φ h * f ((n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x) *
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n : GA D B.V)))) * hn1
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_mul_right_N B _ hG y]

theorem per_flagN {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) :
    B.per ψ φ (rTrans x f) = psiBes ψ B.d 1 (vecB B.o B.ζ) x * B.per ψ φ f := by
  unfold BesLev.per besPer
  simp_rw [inner_N B ψ hψ.1 φ f hf hx]
  exact integral_const_mul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_embA (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {g : GL n k}
    {h : GA D B.A} (hh : p.IsLoc FA h g) : p.IsLoc F (GlobalTheory.MixPer.embA B.d B.o h) (embX c g) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [GlobalTheory.MixPer.embA_apply]
  refine ⟨GlobalTheory.LocGrp.suppAt_wittLeviEmbedding B.d (GlobalTheory.LocGrp.suppAt_emb B.o hh.1),
    GlobalTheory.LocGrp.eq_embX F _ g ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (GlobalTheory.LocGrp.intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r =>
      (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩
      (hY _ j (by simp only; omega))

end GlobalTheory.NormalFramePeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_phi_inner_product : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.NrmVol.phiQ_ip | exact GlobalTheory.NrmVol.phiQ_ip | (intros; apply GlobalTheory.NrmVol.phiQ_ip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isHeight_hgtStd : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → IsHeight (hgtStd A a κ p) := by
  intro D A μ hμ κ hκ a p hc p₁ hp₁ α hα k hk
  have hq : κ.symm p₁ ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ (κ.symm p₁)).2 (by simpa using hp₁)
  set q : siegel A := ⟨κ.symm p₁, hq⟩ with hqdef
  have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hc]; simpa [mul_assoc] using hk
  have e : κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹ =
      ((q * p⁻¹ : siegel A) : GA D (dblSp A)) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) := by
    simp [hqdef, map_mul, mul_assoc]
  have hdet : aP A q = Matrix.GeneralLinearGroup.det α :=
    GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ q α (by simpa [hqdef] using hα)
  show hgt A a (κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹) * absA D (aP A p) = absA D (Matrix.GeneralLinearGroup.det α)
  rw [e, hgt_mul A a (q * p⁻¹) hk', ← map_mul, ← map_mul, inv_mul_cancel_right, hdet]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  first | exact @GlobalTheory.ChainOnto.partPar | exact GlobalTheory.ChainOnto.partPar | (intros; apply GlobalTheory.ChainOnto.partPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  first | exact @GlobalTheory.ChainOnto.parBound_of_rapidDecay | exact GlobalTheory.ChainOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.ChainOnto.parBound_of_rapidDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsBiSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_contraction_isBiSmooth : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiSmooth (contr l S vL f₁ f₂) := by
  first | exact @GlobalTheory.ContrSmooth.contr_isBiSmooth | exact GlobalTheory.ContrSmooth.contr_isBiSmooth | (intros; apply GlobalTheory.ContrSmooth.contr_isBiSmooth <;> assumption)
end

