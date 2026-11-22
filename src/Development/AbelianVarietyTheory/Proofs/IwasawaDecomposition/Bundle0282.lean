import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RealGeo.Upd

section
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section
variable (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (kap lam err)

abbrev upE : RealDat D A C.Q.c.F := { R.upd6 kap lam with err0 := err }

set_option maxHeartbeats 1600000 in

def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat C.toCore R i Tp tup) :
    OMDat C.toCore (upE C R kap lam err) i Tp tup := { O with }

set_option maxHeartbeats 1600000 in

def updFWT {κ v₀} (t : FWTie C R κ v₀) : FWTie C (upE C R kap lam err) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

variable {C R}
variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (O : ∀ i, OMDat C.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in

theorem omPins_upE (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (upE C R kap lam err) κ v₀ (fun i => updO C R kap lam err (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end

end

end GlobalTheory.RealGeo.Upd

namespace GlobalTheory.RealGeo

set_option maxHeartbeats 1600000 in

theorem geoHalf_upd : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (ph : Fin D.R.m → ℂ) kap lam err (g : GlobalTheory.RealGeo.GeoHalf C R ph), ∃ g' : GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph, g'.κ = g.κ ∧ HEq g'.v₀ g.v₀ ∧ (GlobalTheory.RealGeo.InGeo g → GlobalTheory.RealGeo.InGeo g') := by
  intro D G _ _ Pl0 T A C _ R ph kap lam err g
  refine ⟨⟨g.κ, g.v₀, Upd.updFWT C R kap lam err g.fw, g.bar, fun i => Upd.updO C R kap lam err (g.O i),
    fun i => Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩, rfl, HEq.rfl, ?_⟩
  intro h
  exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParDualPar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.FrameModels

theorem card_signs {n p q : ℕ} (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p ∧
      (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = false).card = q := by
  have h1 : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
    have : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true) =
        Finset.univ.map (Fin.castLEEmb (by omega : p ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  refine ⟨h1, ?_⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => decide ((a : ℕ) < p) = true)
  simp only [Bool.not_eq_true] at h2
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega

open Formalism.L2.NTheta in

theorem goodPar_holPar {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    GoodPar n p q (holPar p q (kapW h p q)) := by
  have hs : StrictAnti fun a : Fin n => ((lamAt h a : ℚ) : ℝ) := fun a b hab => by
    have := GlobalTheory.HolDict.lamAt_strictAnti h hn hab
    show ((lamAt h b : ℚ) : ℝ) < ((lamAt h a : ℚ) : ℝ)
    exact_mod_cast this
  refine ⟨fun a => (lamAt h a : ℝ), fun a => decide ((a : ℕ) < p), ⟨hs, fun a => lamAt h a, fun a => rfl,
    GlobalTheory.HolDict.holPar_kapW_eq h hn hpq⟩, ⟨hs, fun a => ?_⟩, (card_signs hpq).1, (card_signs hpq).2⟩
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs'⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  have hn' : ((n : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs']; push_cast; rfl
  show ((lamAt h a : ℚ) : ℝ) - _ = _
  rw [hz, hn']
  push_cast
  ring

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hl, r, hr, hS⟩, ⟨-, hi⟩, hp, hq⟩ := h
  have hs : StrictAnti fun a => -lam (Fin.rev a) := fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab))
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a), ⟨hs, fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩,
    ⟨hs, fun a => ?_⟩, ?_, ?_⟩
  · rw [hS]
    ext z
    simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩
  · obtain ⟨m, hm⟩ := hi (Fin.rev a)
    refine ⟨-m - n + 1, ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by simp)

variable {D : D7}

theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) :
    ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := by
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _, rank_Wc i]
  have := D.R.m_add_three_le_k
  have hi := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem goodPar_parAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    GoodPar (Wc D i).rank ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (parAt (Wc D i) σ ρ) := by
  have h := goodPar_holPar (D.hc (lab σ ρ)) (rank_Wc i) (sig_add i ρ)
  unfold Links.parAt
  split_ifs
  · exact h
  · exact goodPar_dualPar h

theorem parAt_congr (W : HSp D) {σ σ' : D.what₂.LL →+* ℂ} (h : labE σ = labE σ') : parAt W σ = parAt W σ' := by
  have hl : lab σ = lab σ' := by
    funext ρ
    unfold lab
    rw [h]
  funext ρ
  unfold Links.parAt kapAt
  rw [h, hl]

theorem exists_frameKs : GlobalTheory.Published.DiscreteSeriesExists → ∀ (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x, D.embE x ∈ (algebraMap Ks D.what₂.LL).range) → ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ), FrameKs Ks MW := by
  intro hP D Ks _ _ hK
  classical
  have hne : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Nonempty (DSModel (Wc D i) (parAt (Wc D i) σ)) := fun i σ =>
    GlobalTheory.Published.dsExists_of_discreteSeriesExists hP D _ _ (D.sp.W_sig _) (goodPar_parAt i σ)
  have hx : ∀ (V : HSp D) (S S' : D.what₂.Tau → SPar) (h : Nonempty (DSModel V S)) (h' : Nonempty (DSModel V S')), S = S' →
      ∀ ρ, x0Mat (Classical.choice h) ρ = x0Mat (Classical.choice h') ρ := by
    intro V S S' h h' e ρ
    subst e
    rfl
  refine ⟨fun i σ => Classical.choice (hne i σ), fun i σ σ' hσ ρ => hx _ _ _ _ _ (parAt_congr _ ?_) ρ, fun i σ hσ τ a => ?_⟩
  · funext τ
    ext x
    obtain ⟨y, hy⟩ := hK (D.host.sigmaOf (D.eTau τ).1 x)
    show σ (D.embE (D.host.sigmaOf (D.eTau τ).1 x)) = σ' (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rw [← hy]
    exact RingHom.congr_fun hσ y
  · have he := (Classical.choice (hne i σ)).enum τ
    have e : parAt (Wc D i) σ τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ τ) := if_pos (hσ τ)
    rw [e] at he
    exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (sig_add i τ) he a).2

end GlobalTheory.RealGeo.FrameModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarInfiniteGLLtTopOfInfiniteGLHaarMeasureLtTop
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.HaarFinVol

open GlobalTheory.FlagMeas

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def entP (y : GL (Fin j) (Cinf E)) : InfinitePlace E → Fin j → Fin j → ℂ :=
  fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w

def ent (y : GL (Fin j) (Cinf E)) : MatInf E j := entP E j y

def swapH : Matrix (Fin j) (Fin j) (Cinf E) ≃ₜ (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun M w a b := M a b w
  invFun x := Matrix.of fun a b w => x w a b
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun w => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun w =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply w))

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin j) (Cinf E) → Matrix (Fin j) (Fin j) (Cinf E)) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin j) (α := Cinf E)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin j) (R := ℂ) (α := Cinf E)
  have : CompleteSpace (Matrix (Fin j) (Fin j) (Cinf E)) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

theorem isOpenEmbedding_entP : IsOpenEmbedding (entP E j) :=
  (swapH E j).isOpenEmbedding.comp (isOpenEmbedding_val E j)

theorem ent_mul (x y : GL (Fin j) (Cinf E)) : ent E j (x * y) = ent E j x * ent E j y := by
  funext w a b
  change (((x * y : GL (Fin j) (Cinf E)) : Matrix (Fin j) (Fin j) (Cinf E)) a b w) =
    (Matrix.of (ent E j x w) * Matrix.of (ent E j y w)) a b
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_apply]
  rfl

theorem detNorm_ent_pos (y : GL (Fin j) (Cinf E)) : 0 < detNorm E j (ent E j y) := by
  unfold detNorm
  refine Finset.prod_pos fun w _ => ?_
  have h1 : Matrix.of (ent E j y w) =
      (y : Matrix (Fin j) (Fin j) (Cinf E)).map (Pi.evalRingHom (fun _ => ℂ) w) := by
    ext a b; rfl
  have h2 : (Matrix.of (ent E j y w)).det = (y : Matrix (Fin j) (Fin j) (Cinf E)).det w := by
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hu : IsUnit (y : Matrix (Fin j) (Fin j) (Cinf E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have h3 : (y : Matrix (Fin j) (Fin j) (Cinf E)).det w ≠ 0 :=
    (hu.map (Pi.evalRingHom (fun _ => ℂ) w)).ne_zero
  rw [h2]
  positivity

theorem haarGL_lt_top_of_isCompact (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsCompact S)
    (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S < ⊤ := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; exact (measure_empty (μ := haarGL E j)).trans_lt ENNReal.zero_lt_top
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hd.continuousOn
  have hm := hpos x0 hx0
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S < ⊤
  rw [withDensity_apply _ hS.isClosed.measurableSet]
  refine (setLIntegral_mono' hS.isClosed.measurableSet
    (g := fun _ => ENNReal.ofReal ((detNorm E j x0)⁻¹ ^ j)) fun x hx => ?_).trans_lt ?_
  · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.2 (hpos x hx).le)
      (inv_anti₀ hm (hmin hx)) j)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top

theorem haarGL_ne_zero_of_isOpen (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsOpen S)
    (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S ≠ 0 := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S ≠ 0
  have hf : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    ((hd.measurable.inv).pow_const j).ennreal_ofReal
  rw [Ne, withDensity_apply_eq_zero' hf.aemeasurable]
  have : {x : InfinitePlace E → Fin j → Fin j → ℂ | ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) ≠ 0} ∩ S = S :=
    Set.inter_eq_right.2 fun x hx => (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos x hx)) j)).ne'
  rw [this]
  exact hS.measure_ne_zero volume hne

theorem haarGL_image_mul (a : MatInf E j) (ha : 0 < detNorm E j a) (T : Set (MatInf E j)) :
    haarGL E j ((fun g => a * g) '' T) = haarGL E j T := by
  obtain ⟨hemb, hmp⟩ := GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j a ha
  have := hemb.map_apply (haarGL E j) ((fun g => a * g) '' T)
  rw [hmp.map_eq, Set.preimage_image_eq T hemb.injective] at this
  exact this

variable [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))]

theorem measurableEmbedding_ent : MeasurableEmbedding (ent E j) :=
  (isOpenEmbedding_entP E j).measurableEmbedding

def nuGL : Measure (GL (Fin j) (Cinf E)) := (haarGL E j).comap (ent E j)

theorem nuGL_apply (s : Set (GL (Fin j) (Cinf E))) : nuGL E j s = haarGL E j (ent E j '' s) :=
  (measurableEmbedding_ent E j).comap_apply _ s

theorem isHaarMeasure_nuGL : (nuGL E j).IsHaarMeasure := by
  have he := isOpenEmbedding_entP E j
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [nuGL_apply]
    refine haarGL_lt_top_of_isCompact E j (entP E j '' K) (hK.image he.continuous) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y
  · intro g
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, nuGL_apply, nuGL_apply]
    have e1 : (fun h => g * h) ⁻¹' s = (fun h => g⁻¹ * h) '' s := by
      ext y; simp [Set.mem_image, eq_inv_mul_iff_mul_eq]
    have e2 : ent E j '' ((fun h => g⁻¹ * h) '' s) =
        (fun x : MatInf E j => ent E j g⁻¹ * x) '' (ent E j '' s) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => ent_mul E j g⁻¹ y
    rw [e1, e2, haarGL_image_mul E j _ (detNorm_ent_pos E j g⁻¹)]
  · intro U hU hne
    rw [nuGL_apply]
    refine haarGL_ne_zero_of_isOpen E j (entP E j '' U) (he.isOpenMap U hU) (hne.image _) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y

end GlobalTheory.HaarFinVol

theorem GlobalTheory.haarGL_finite_pullback : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  intro E _ _ j _ _ ν _ D _ hD
  haveI := GlobalTheory.HaarFinVol.isHaarMeasure_nuGL E j
  have he := GlobalTheory.HaarFinVol.isOpenEmbedding_entP E j
  haveI : LocallyCompactSpace (GL (Fin j) (Cinf E)) := he.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin j) (Cinf E)) := he.isEmbedding.secondCountableTopology
  have h2 : GlobalTheory.HaarFinVol.nuGL E j {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w :
      GlobalTheory.FlagMeas.MatInf E j) ∈ D} ≤ GlobalTheory.FlagMeas.haarGL E j D :=
    (GlobalTheory.HaarFinVol.nuGL_apply E j _).trans_le (measure_mono fun _ ⟨_, hy, e⟩ => e ▸ hy)
  rw [Measure.isMulLeftInvariant_eq_smul ν (GlobalTheory.HaarFinVol.nuGL E j), Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h2.trans_lt hD)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory.ChernScale

section General

variable {α : Type*} [MeasurableSpace α] {κ : Sort*}

theorem restrict_iSup_eq (μ : κ → Measure α) {S : Set α} (hS : MeasurableSet S) :
    (⨆ i, μ i).restrict S = ⨆ i, (μ i).restrict S := by
  refine le_antisymm ?_ (iSup_le fun i => Measure.restrict_mono subset_rfl (le_iSup μ i))
  have h : (⨆ i, μ i) ≤ (⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ i) hS, Measure.add_apply, Measure.add_apply]
    exact add_le_add (Measure.le_iff'.1 (le_iSup (fun i => (μ i).restrict S) i) B)
      (Measure.le_iff'.1 (Measure.restrict_mono subset_rfl (le_iSup μ i)) B)
  calc (⨆ i, μ i).restrict S ≤ ((⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ).restrict S :=
        Measure.restrict_mono subset_rfl h
    _ = (⨆ i, (μ i).restrict S).restrict S := by
        rw [Measure.restrict_add, Measure.restrict_restrict hS, Set.inter_compl_self,
          Measure.restrict_empty, add_zero]
    _ ≤ _ := Measure.restrict_le_self

theorem smul_iSup_eq (ν : κ → Measure α) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c • (⨆ i, ν i) = ⨆ i, c • ν i := by
  have mono : ∀ (d : ℝ≥0∞) {μ μ' : Measure α}, μ ≤ μ' → d • μ ≤ d • μ' := fun d μ μ' h =>
    Measure.le_iff.2 fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl <| Measure.le_iff'.1 h s
  rcases eq_or_ne c 0 with rfl | h0
  · simp only [zero_smul]
    exact (le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)).symm
  refine le_antisymm ?_ (iSup_le fun i => mono c (le_iSup ν i))
  have key : (⨆ i, ν i) ≤ c⁻¹ • ⨆ i, c • ν i := iSup_le fun i => by
    calc ν i = c⁻¹ • c • ν i := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      _ ≤ _ := mono _ (le_iSup (fun i => c • ν i) i)
  calc c • (⨆ i, ν i) ≤ c • c⁻¹ • ⨆ i, c • ν i := mono c key
    _ = _ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hc, one_smul]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ}

theorem chartMeas_restrict_eq (e : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S) (h : ∀ y ∈ e.source, y ∈ S → ρ y = c * ρ' y) :
    (chartMeas e ρ).restrict S = c • (chartMeas e ρ').restrict S := by
  ext B hB
  rw [Measure.smul_apply, Measure.restrict_apply hB, Measure.restrict_apply hB, smul_eq_mul,
    chartMeas_apply e ρ (hB.inter hS), chartMeas_apply e ρ' (hB.inter hS), ← lintegral_const_mul' c _ hc]
  refine setLIntegral_congr_fun (measurableSet_image e (e.open_source.measurableSet.inter (hB.inter hS))
    Set.inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  show ρ (e.symm (e y)) = c * ρ' (e.symm (e y))
  rw [e.left_inv hy.1]
  exact h y hy.1 hy.2.2

theorem glueMeas_restrict_eq {ι : Type*} (e : ι → OpenPartialHomeomorph X (V n)) {ρ ρ' : ι → X → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = c * ρ' i y) :
    (glueMeas e ρ).restrict S = c • (glueMeas e ρ').restrict S := by
  rw [glueMeas, glueMeas, restrict_iSup_eq _ hS, restrict_iSup_eq _ hS, smul_iSup_eq _ hc]
  exact iSup_congr fun i => chartMeas_restrict_eq (e i) hc hS (h i)

end General

end GlobalTheory.ChernScale

namespace GlobalTheory.GoodMetric

open GlobalTheory.ChernScale

theorem hasChernIntegral_of_eq_mul : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R R₀ : MvPolynomial (ι × ℕ) ℝ) (t v : ℝ),
    (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      chernTop R (fun w => H A (c.e.symm w)) (c.e y) = t * chernTop R₀ (fun w => H A (c.e.symm w)) (c.e y)) →
    HasChernIntegral E O H R₀ v → HasChernIntegral E O H R (t * v) := by
  intro F _ σ X ι m E O H R R₀ t v hRt hv
  have hP : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have key : ∀ (ε ε' : ℤˣ) (c : ℝ), 0 ≤ c → (∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) →
      chernTopPart E H R ε (ptsIn X.str σ O) =
        ENNReal.ofReal c * chernTopPart E H R₀ ε' (ptsIn X.str σ O) := by
    intro ε ε' c hc hx
    have hm : (chernTopPart E H R ε).restrict (ptsIn X.str σ O) =
        ENNReal.ofReal c • (chernTopPart E H R₀ ε').restrict (ptsIn X.str σ O) :=
      glueMeas_restrict_eq _ ENNReal.ofReal_ne_top hP fun a y hy hyS => ?_
    · have := congrArg (fun μ : Measure (CxPts X.str σ) => μ (ptsIn X.str σ O)) hm
      simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using this
    · have e1 := hRt y hyS a hy _ (E.nonempty (under y)).choose_spec
      beta_reduce
      rw [e1, hx, ENNReal.ofReal_mul hc]
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε ε t ht (fun x => by ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 ε)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 1 t ht (fun x => by ring), key (-1) (-1) t ht (fun x => by ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      ring
  · have ht' : 0 ≤ -t := by linarith
    refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε (-ε) (-t) ht' (fun x => by rw [Units.val_neg, Int.cast_neg]; ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 _)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 (-1) (-t) ht' (fun x => by push_cast; ring), key (-1) 1 (-t) ht' (fun x => by push_cast; ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht']
      ring

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  first | exact @GlobalTheory.CuspRep.CompUniq.isotypic | exact GlobalTheory.CuspRep.CompUniq.isotypic | (intros; apply GlobalTheory.CuspRep.CompUniq.isotypic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphismStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  first | exact @GlobalTheory.FlagBundle.ProjBundle.affCover | exact GlobalTheory.FlagBundle.ProjBundle.affCover | (intros; apply GlobalTheory.FlagBundle.ProjBundle.affCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleCompStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlagRefinementBundle_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) := by
  first | exact @GlobalTheory.FlagBundle.refines_comp | exact GlobalTheory.FlagBundle.refines_comp | (intros; apply GlobalTheory.FlagBundle.refines_comp <;> assumption)
end

