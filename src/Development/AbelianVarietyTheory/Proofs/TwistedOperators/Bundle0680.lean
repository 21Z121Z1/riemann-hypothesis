import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0548
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0549
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul' (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem map_eq_one_of_off {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F))) : (Formalism.L2.Theta.mt V g).map p.π = 1 := by
  ext i k
  have h0 := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ g).1 hg i k _ rfl
  have h1 : p.π ((Formalism.L2.Theta.mt V g - 1) i k) = 0 := by
    rw [hp.2.1]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt _ _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero _ _ h0) w rfl
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1, ← Matrix.map_apply (f := p.π), Matrix.map_one _ (map_zero _) (map_one _)]

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem suppAt_mul' {e : AE D} {V : HSp D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) : SuppAt e V (a * b) := by
  rw [suppAt_iff'] at ha hb ⊢
  have : Formalism.L2.Theta.mt V (a * b) - 1 = (Formalism.L2.Theta.mt V a - 1) * Formalism.L2.Theta.mt V b + (Formalism.L2.Theta.mt V b - 1) := by
    rw [mt_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, ← smul_mul_assoc, ha, hb]

theorem suppAt_inv' {e : AE D} {V : HSp D} {a : GA D V} (ha : SuppAt e V a) : SuppAt e V a⁻¹ := by
  rw [suppAt_iff'] at ha ⊢
  have : Formalism.L2.Theta.mt V a⁻¹ - 1 = -(Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a - 1)) := by
    rw [Matrix.mul_sub, mt_inv_mul', Matrix.mul_one]; abel
  rw [this, smul_neg, ← mul_smul_comm, ha]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem isLoc_mul' {S : HSp D} {F : Frame k S.rank Y} {a b : GA D S} {x y : GL Y k} (ha : p.IsLoc F a x)
    (hb : p.IsLoc F b y) : p.IsLoc F (a * b) (x * y) := by
  refine ⟨suppAt_mul' ha.1 hb.1, ?_⟩
  rw [mt_mul', Matrix.map_mul, ha.2, hb.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem isLoc_inv' {S : HSp D} {F : Frame k S.rank Y} {a : GA D S} {x : GL Y k} (ha : p.IsLoc F a x) :
    p.IsLoc F a⁻¹ x⁻¹ := by
  refine ⟨suppAt_inv' ha.1, ?_⟩
  have h1 : (Formalism.L2.Theta.mt S a⁻¹).map p.π * (F.β * x.val * F.γ) = 1 := by
    rw [← ha.2, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  calc (Formalism.L2.Theta.mt S a⁻¹).map p.π = (Formalism.L2.Theta.mt S a⁻¹).map p.π * ((F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ)) := by
        rw [h2, Matrix.mul_one]
    _ = F.β * (x⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit p in
theorem frOf_conj {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D)) :
    (frOf h β w).β * (GlobalTheory.FunObj.inBasis h β w x).val * (frOf h β w).γ = (loc w x).val := by
  subst h
  have e1 : (frOf rfl β w).β = (loc w β).val := by ext i j; rfl
  have e2 : (frOf rfl β w).γ = ((loc w β)⁻¹).val := by ext i j; rfl
  have e3 : GlobalTheory.FunObj.inBasis rfl β w x = (loc w β)⁻¹ * loc w x * loc w β := by
    have e4 : GlobalTheory.FunObj.inBasis rfl β w x = GlobalTheory.StepData.reGL (finCongr rfl) (loc w (β⁻¹ * x * β)) := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e5 : ∀ g : GL (Fin N) (Kw w), GlobalTheory.StepData.reGL (finCongr rfl) g = g := fun g => Units.ext (by ext i j; rfl)
    rw [e4, e5, map_mul, map_mul, map_inv]
  rw [e1, e2, e3, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.FlatPlaceLoc

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem loc_finE {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} (g : GA D V) :
    (loc w (Lev.finE V g)).val = (Formalism.L2.Theta.mt V g).map p.π := by
  ext i j
  rw [Matrix.map_apply, hp.2.1]
  rfl

theorem isLoc_of_inBasis {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {N : ℕ} (h : N = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (gk : GL (Fin N) (Kw w)) (hs : SuppAt p.e V g)
    (hb : GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) = gk) : p.IsLoc (frOf h β w) g gk :=
  ⟨hs, by rw [← hb, frOf_conj, loc_finE hp]⟩

theorem elt_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) :
    (repsAt G t w).elt β (D.R.m, 0) = stair (locGrid G t w) (unifAt w) (cosExp G w) 0 :=
  (onColumn_apply (G := locGrid G t w) _ 0).trans rfl

open Classical in

theorem localization₂ : Big fun ch => LocP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp β r r₀ h hpts j hj
  obtain ⟨hr, hr₀, hh⟩ := hpts
  have L1 : p.IsLoc (frRow ch.S.B t w j hj) (r j) _ := isLoc_of_inBasis hp _ _ _ _ (hr j hj).1 (hr j hj).2
  have L0 : p.IsLoc (frRow ch.S.B t w j hj) (r₀ j) _ := isLoc_of_inBasis hp _ _ _ _ (hr₀ j hj).1 (hr₀ j hj).2
  refine ⟨?_, fun he => ?_, fun ho => ?_⟩
  · convert isLoc_mul' p (isLoc_inv' p L0) L1 using 1
    beta_reduce
    rw [Pi.mul_apply]
    by_cases h0 : j = 0
    · subst h0
      have hn : (0 : ℕ) ∉ idx D := by rw [mem_idx]; omega
      rw [if_pos rfl, if_neg hn, epsV_apply, if_neg hn, one_mul, elt_zero]
      exact (inv_inv _).symm.trans (mul_one _).symm
    · by_cases hi : j ∈ idx D
      · rw [if_neg h0, if_pos hi, inv_one, one_mul, epsV_apply, if_pos hi]
      · have hm : D.R.m ≤ j + 1 := by rw [mem_idx] at hi; omega
        rw [if_neg h0, if_neg hi, inv_one, mul_one, epsV_eq_one t w hm, elt_eq_one t w β hm, mul_one]
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    rw [hδ.2.1 he, inv_one, one_mul] at hoff
    rw [mt_mul', Matrix.map_mul, map_eq_one_of_off hp hoff, Matrix.one_mul, L0.2, Matrix.mul_assoc,
      (frRow ch.S.B t w j hj).γβ, Matrix.mul_one]
    rfl
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    refine ⟨δ, hδ, ?_⟩
    have h0 : j ≠ 0 := by rintro rfl; simp at ho
    have hr0 : (Formalism.L2.Theta.mt _ (r₀ j)).map p.π = 1 := by
      rw [L0.2]
      simp only [if_neg h0, Units.val_one, Matrix.mul_one, (frRow ch.S.B t w j hj).βγ]
    rw [mt_mul', Matrix.map_mul, hr0, Matrix.mul_one, ← mul_inv_cancel_left δ (h j), mt_mul', Matrix.map_mul,
      map_eq_one_of_off hp hoff, Matrix.mul_one]

end GlobalTheory.FlatPlaceLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Chain (ptOf)
open GlobalTheory.Chain.RealIt (glue)

namespace GlobalTheory.EvenOntoRealZeta

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in

theorem realZeta : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  intro hDS hHC D c hc k hk s s' hs hs' p hp m X hmX
  have hvac := hp.pre.vac
  have hW := hp.pre.weil
  have hArch := fun τ =>
    (GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) (hp.pre.par τ)).1 τ s.V s'.V
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hLL := fun τ => (hArch τ).1 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ)
  have hZL := fun τ => (hArch τ).2 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, fun τ => hwk τ, ?_⟩
  intro mR hmR z
  have hfac := GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · intro a ha hfr
    have htpos : 0 < c.t := by have := hc.step; omega
    refine ⟨0, div_pos (by exact_mod_cast htpos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
      a ha hfr (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one (fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : c.t ≤ s'.V.rank := by
      rw [hs'.rank]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor mR z mf Hf C s'.V.rank c.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.EvenOntoRealZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

private theorem B_update_mul_eq_mul {X : ℕ → Type} (B : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (j : ℕ)
    (a : (∀ i, X i) → X j → ℂ) (R : (∀ i, X i) → ℂ)
    (ha : ∀ u x, a (Function.update u j x) = a u) (hR : ∀ u x, R (Function.update u j x) = R u)
    (u : ∀ i, X i) :
    B j (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) (u j) =
      B j (a u) (u j) * R u := by
  have hfun : (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) =
      R u • a u := by
    funext x
    rw [ha, hR, Function.update_self, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prod_op {X : ℕ → Type} (A : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (n : ℕ) :
    ∃ Tc : ((∀ j, X j) → ℂ) →ₗ[ℂ] ((∀ j, X j) → ℂ), ∀ (C : ∀ j, X j → X (j + 1) → ℂ) (g : (∀ j, X j) → ℂ),
      (∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g u = g u') →
      (fun u : ∀ j, X j => (∏ k ∈ Finset.range n,
          A (2 * k) (fun x => A (2 * k + 1) (C (2 * k) x) (u (2 * k + 1))) (u (2 * k))) * g u) =
        Tc (fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) := by
  classical

  let op : ∀ j, ((∀ i, X i) → ℂ) →ₗ[ℂ] ((∀ i, X i) → ℂ) := fun j =>
    { toFun := fun F u => A j (fun x => F (Function.update u j x)) (u j)
      map_add' := fun F G => by
        funext u
        have e : (fun x => (F + G) (Function.update u j x)) =
            (fun x => F (Function.update u j x)) + (fun x => G (Function.update u j x)) := rfl
        rw [e, map_add]
        rfl
      map_smul' := fun c F => by
        funext u
        have e : (fun x => (c • F) (Function.update u j x)) = c • (fun x => F (Function.update u j x)) := rfl
        rw [e, map_smul]
        rfl }
  induction n with
  | zero => exact ⟨LinearMap.id, fun C g _ => by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T ∘ₗ op (2 * n) ∘ₗ op (2 * n + 1), fun C g hg => ?_⟩

    obtain ⟨R, hRR⟩ : ∃ R : (∀ j, X j) → ℂ,
        R = fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u := ⟨_, rfl⟩
    have hR : ∀ j, 2 * n ≤ j → j < 2 * n + 2 → ∀ (u : ∀ i, X i) x, R (Function.update u j x) = R u := by
      intro j hj1 hj2 u x
      subst hRR
      dsimp only
      congr 1
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact hg _ _ fun i hi => Function.update_of_ne (by omega) _ _

    obtain ⟨g', hgG⟩ : ∃ g' : (∀ j, X j) → ℂ,
        g' = fun u => A (2 * n) (fun x => A (2 * n + 1) (C (2 * n) x) (u (2 * n + 1))) (u (2 * n)) * g u :=
      ⟨_, rfl⟩
    have hg' : ∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g' u = g' u' := by
      intro u u' h
      subst hgG
      dsimp only
      rw [h (2 * n) le_rfl, h (2 * n + 1) (by omega), hg u u' fun j hj => h j (by omega)]

    have h1 : op (2 * n + 1) (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
        fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u := by
      have hF : (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
          fun u => (fun w : ∀ j, X j => C (2 * n) (w (2 * n))) u (u (2 * n + 1)) * R u := by
        funext u
        subst hRR
        simp only [Finset.prod_range_succ]
        ring
      rw [hF]
      funext v
      refine B_update_mul_eq_mul A (2 * n + 1) (fun w => C (2 * n) (w (2 * n))) R ?_ (hR _ (by omega) (by omega)) v
      intro w x
      show C (2 * n) (Function.update w (2 * n + 1) x (2 * n)) = C (2 * n) (w (2 * n))
      rw [Function.update_of_ne (by omega)]

    have h2 : op (2 * n) (fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u) =
        fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g' u := by
      funext v
      have e := B_update_mul_eq_mul A (2 * n) (fun w x => A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))) R
        (fun w y => by
          funext x
          show A (2 * n + 1) (C (2 * n) x) (Function.update w (2 * n) y (2 * n + 1)) = A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))
          rw [Function.update_of_ne (by omega)])
        (hR _ le_rfl (by omega)) v
      refine e.trans ?_
      subst hRR hgG
      dsimp only
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, ← hT C g' hg']
    funext u
    subst hgG
    simp only [Finset.prod_range_succ]
    ring

noncomputable def combLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem exists_comb_op : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ => ?_⟩⟩
  intro c
  obtain ⟨Tc, hTc⟩ := exists_prod_op (X := fun j => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
    (fun j => combLin ch.W.ψ _ _ (c.1 j)) (D.R.m / 2)
  refine ⟨Tc, fun C => ?_⟩
  exact hTc C (fun _ => ∏ i, (1 : SchRow ch.G) i ((0 : RowPt ch.G) i)) fun _ _ _ => rfl

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_line_operator_polynomial : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @GlobalTheory.DerPol.exists_lieDer_model' | exact GlobalTheory.DerPol.exists_lieDer_model' | (intros; apply GlobalTheory.DerPol.exists_lieDer_model' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_coefficientField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverField.pinsOverL | exact GlobalTheory.PinsOverField.pinsOverL | (intros; apply GlobalTheory.PinsOverField.pinsOverL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFlatLaws

theorem flatS_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y _ f hf
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  refine ⟨fun N hN => ?_, fun ξ => ?_⟩
  · exact GlobalTheory.FlatShiftPf.flatAt_shift hψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν s.vU.unit.1 _ _ f N hN
  · exact GlobalTheory.FlatLawsDuality.flatAt_iso dV dW s.vS s.vT s.vU.ν _ _ hψ f hf ξ

end GlobalTheory.AscFlatLaws

end
end

