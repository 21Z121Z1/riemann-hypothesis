import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDatComb

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem conjI_eq_comap (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMax (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ bar_surj

theorem conjI_inj {P P' : Ideal (𝓞 D.host.E)} (h : conjI P = conjI P') : P = P' := by
  ext a
  have := SetLike.ext_iff.1 h (GlobalTheory.SW.Lev.bar a)
  rwa [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this

theorem mem_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E} :
    x ∈ liftI Pg Q ↔ ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∈ PP.asIdeal := by
  constructor
  · intro hx PP hPP
    exact GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le hPP hx)
  · intro h
    unfold liftI
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Submodule.mem_iInf]
      intro PP hPP
      exact GlobalTheory.SW.Lev.mem_conjI.2 (h PP hPP)
    · intro PP _ PP' _ hne
      have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun e =>
        hne (HeightOneSpectrum.ext (conjI_inj e))
      exact (Ideal.isCoprime_iff_sup_eq).2 ((conjI_isMax PP).coprime_of_ne (conjI_isMax PP') hne')

theorem isUnit_mk_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E}
    (h : ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∉ PP.asIdeal) : IsUnit (Ideal.Quotient.mk (liftI Pg Q) x) := by
  have hc : IsCoprime (Ideal.span {x}) (liftI Pg Q) := by
    unfold liftI
    refine IsCoprime.prod_right fun PP hPP => ?_
    have hx : x ∉ conjI PP.asIdeal := fun hm => h PP hPP (GlobalTheory.SW.Lev.mem_conjI.1 hm)
    obtain ⟨y, i, hi, e⟩ := (conjI_isMax PP).exists_inv hx
    exact Ideal.isCoprime_iff_exists.2 ⟨y * x, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x), i, hi, e⟩
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ a, ?_⟩
  have : Ideal.Quotient.mk (liftI Pg Q) j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
  rw [← map_mul, mul_comm, eq_sub_of_add_eq e, map_sub, this, sub_zero, map_one]

section CongLemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem cong_of_sub_mem {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} (h : u - v ∈ 𝔪 • X.Λ) : GlobalTheory.SW.Cong X 𝔪 u v :=
  ⟨1, by rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq], by rwa [one_smul]⟩

theorem cong_congr_left {𝔪 : Ideal (𝓞 E)} {y u v : Fin r → E} (hy : y - u ∈ 𝔪 • X.Λ)
    (h : GlobalTheory.SW.Cong X 𝔪 y v) : GlobalTheory.SW.Cong X 𝔪 u v := by
  obtain ⟨s, hs, hm⟩ := h
  refine ⟨s, hs, ?_⟩
  have : s • (u - v) = s • (y - v) - s • (y - u) := by
    rw [← smul_sub]; congr 1; abel
  rw [this]
  exact sub_mem hm (Submodule.smul_mem _ s hy)

theorem sum_mem_of_coeff {𝔪 : Ideal (𝓞 E)} {m : ℕ} (β : Fin m → Fin r → E) (hβ : ∀ i, β i ∈ X.Λ)
    (d : Fin m → 𝓞 E) (hd : ∀ j, d j ∈ 𝔪) : ∑ j, d j • β j ∈ 𝔪 • X.Λ :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hd j) (hβ j)

end CongLemmas

section Mat
open GlobalTheory.LiftLevel GlobalTheory.LiftDat
variable {D : D7}

theorem mk_conjI_eq_iff (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) :
    Ideal.Quotient.mk (conjI P) x = Ideal.Quotient.mk (conjI P) y ↔
      Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar x) = Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar y) := by
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq, GlobalTheory.SW.Lev.mem_conjI, map_sub]

theorem mapMat_eq_one_iff {R' : Type*} [CommRing R'] {r : ℕ} (f : 𝓞 D.host.E →+* R')
    (A : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    A.map f = 1 ↔ ∀ a b, f (A a b) = f ((1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) a b) := by
  rw [← Matrix.map_one f (map_zero f) (map_one f), ← Matrix.ext_iff]
  simp only [Matrix.map_apply]

theorem jgrp_iff {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} (κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q))
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (hκ : κ.val = ctᵀ.map (Ideal.Quotient.mk _)) :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP ∈ Pg, ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar) = 1 := by
  rw [mem_Jgrp]
  refine forall₂_congr fun PP hPP => ?_
  rw [Units.ext_iff]
  have e1 : ((Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ hPP)) κ :
      GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = ct.transpose.map (Ideal.Quotient.mk (conjI PP.asIdeal)) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, hκ]
    rfl
  rw [e1, Units.val_one, Matrix.transpose_map, Matrix.transpose_eq_one, mapMat_eq_one_iff, mapMat_eq_one_iff]
  exact forall₂_congr fun a b => mk_conjI_eq_iff _ _ _

theorem conjRes_det {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) {r : ℕ}
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    conjRes Pg Q PP h (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det =
      (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_map, Matrix.transpose_map, Matrix.det_transpose]
  rfl

end Mat

end GlobalTheory.LiftDatComb

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftDatComb GlobalTheory.LiftLevel

theorem dat_mkLevel_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  intro D S T C hn Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 hind y c hyc Y hY
  set ct : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E) := fun a b => c (Fin.castLE hn a) b with hct
  have hTop : ∀ PP ∈ Pg ∪ Q, topL T.rank (Y PP) = ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) := by
    intro PP hPP
    ext a b
    rw [topL, dif_pos ⟨lt_of_lt_of_le a.2 hn, b.2⟩, hY PP hPP]
    rfl
  have hcong0 : ∀ i, GlobalTheory.SW.Cong C.X (liftI Pg Q) (y i) 0 ↔ ∀ j, c i j ∈ liftI Pg Q := by
    intro i
    constructor
    · intro hc
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc i) hc
      exact hind (c i) ⟨s, hs, hm⟩
    · intro hc
      refine cong_of_sub_mem C.X ?_
      rw [sub_zero, ← sub_add_cancel (y i) (∑ j, c i j • β j)]
      exact add_mem (hyc i) (sum_mem_of_coeff C.X β hβ _ hc)
  have hrow : ∀ PP ∈ Pg ∪ Q, ∀ i j, (Y PP i j = 0 ↔ Lev.bar (c i j) ∈ PP.asIdeal) := by
    intro PP hPP i j
    rw [hY PP hPP, Ideal.Quotient.eq_zero_iff_mem]
  have hdetU : ∀ PP ∈ Pg ∪ Q, IsUnit (topL T.rank (Y PP)).det → Lev.bar ct.det ∉ PP.asIdeal := by
    intro PP hPP hu hm
    have e : (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar)).det =
        ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) ct.det := (RingHom.map_det _ _).symm
    rw [hTop PP hPP, e, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hm] at hu
    exact not_isUnit_zero hu
  set L := mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 with hL
  unfold Level.dat
  by_cases h : (∃ k : L.J, L.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin S.rank, T.rank ≤ (k : ℕ) → GlobalTheory.SW.Cong C.X L.𝔪 (y k) 0
  · rw [dif_pos h]
    obtain ⟨k', hk'm, hk'c⟩ := h.1.choose_spec
    set κ := h.1.choose with hκdef
    have hκval : (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val =
        ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := by
      rw [← hk'm]
      ext a b
      simp only [Matrix.map_apply, Matrix.transpose_apply]
      refine Ideal.Quotient.eq.2 ?_
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc (Fin.castLE hn b)) (hk'c b)
      have := hind (fun j => c (Fin.castLE hn b) j - k' j b)
        ⟨s, hs, by
          convert hm using 2
          simp only [sub_zero, sub_smul, Finset.sum_sub_distrib]
          rfl⟩ a
      rw [← neg_sub]
      exact neg_mem this
    have hJ := (jgrp_iff (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)) ct hκval).1 κ.2
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q :=
      fun i hi => (hcong0 i).1 (h.2 i hi)
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) :=
      fun PP hPP i j hi _ => (hrow PP hPP i j).2 (mem_liftI.1 (hlowc i hi j) PP hPP)
    have hdetQ : ∀ PP (hPP : PP ∈ Pg ∪ Q), conjRes Pg Q PP hPP
        (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val.det = (topL T.rank (Y PP)).det := by
      intro PP hPP
      rw [hκval]
      exact (conjRes_det hPP ct).trans (congrArg Matrix.det (hTop PP hPP).symm)
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := fun PP hPP =>
      ⟨hLow PP (Finset.mem_union_right _ hPP), by
        rw [← hdetQ PP (Finset.mem_union_right _ hPP), ← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Units.isUnit _).map _⟩
    have hK : omegaK Pg Y = 1 := by
      unfold omegaK
      rw [if_pos]
      intro PP hPP
      exact ⟨hLow PP (Finset.mem_union_left _ hPP), by rw [hTop PP (Finset.mem_union_left _ hPP)]; exact hJ PP hPP⟩
    rw [hK, one_mul]
    unfold omegaQ
    rw [dif_pos hQc]
    show ((lamHom Pg Q T.rank ξ (⟨κ.1, κ.2⟩ : Jgrp Pg Q T.rank) : ℂˣ) : ℂ) = _
    rw [lamHom_apply, Units.val_inv_eq_inv_val, Units.coe_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q))) =
        (hQc PP.1 PP.2).2.unit := by
      ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact hdetQ _ _
    rw [e, _root_.zpow_neg_one]
  · rw [dif_neg h]
    symm
    by_contra hne
    have hK : omegaK Pg Y ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank ξ (-1) Y ≠ 0 := right_ne_zero_of_mul hne
    have hKc : ∀ PP ∈ Pg, LowZero T.rank (Y PP) ∧ topL T.rank (Y PP) = 1 := by
      by_contra hc
      exact hK (by unfold omegaK; rw [if_neg hc])
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := by
      by_contra hc
      exact hQ (by unfold omegaQ; rw [dif_neg hc])
    apply h
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) := by
      intro PP hPP
      rcases Finset.mem_union.1 hPP with hP | hP
      exacts [(hKc PP hP).1, (hQc PP hP).1]
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q := fun i hi j =>
      mem_liftI.2 fun PP hPP => (hrow PP hPP i j).1 (hLow PP hPP i j hi j.2)
    have hdet : IsUnit (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
      refine isUnit_mk_liftI fun PP hPP => hdetU PP hPP ?_
      rcases Finset.mem_union.1 hPP with hP | hP
      · rw [(hKc PP hP).2, Matrix.det_one]
        exact isUnit_one
      · exact (hQc PP hP).2
    set κ : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q) :=
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit with hκ
    have hκval : κ.val = ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := IsUnit.unit_spec _
    have hκJ : κ ∈ Jgrp Pg Q T.rank := (jgrp_iff κ ct hκval).2 fun PP hPP => by
      rw [← hTop PP (Finset.mem_union_left _ hPP)]
      exact (hKc PP hPP).2
    exact ⟨⟨⟨κ, hκJ⟩, ctᵀ, hκval.symm, fun i => cong_of_sub_mem C.X (hyc (Fin.castLE hn i))⟩,
      fun k hk => (hcong0 k).2 (hlowc k hk)⟩

end GlobalTheory.LiftDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviCommutesSplitTorus
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd

theorem isSplit_commute_flagM : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W →
    ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → ∀ m ∈ flagM ε W, m * t = t * m := by
  intro n a ε j W hW x t ht m hm
  have hmi : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm
  have hmul : ∀ g h : UJ ε, uMat (g * h) = uMat g * uMat h := fun _ _ => rfl
  have hmm : uMat m * uMat m⁻¹ = 1 := by rw [← hmul, mul_inv_cancel]; rfl
  have hJ : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹ := by
    have hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
    calc (uMat m)ᴴ * Jm ε = (uMat m)ᴴ * Jm ε * (uMat m * uMat m⁻¹) := by rw [hmm, Matrix.mul_one]
      _ = Jm ε * uMat m⁻¹ := by rw [← Matrix.mul_assoc, hg]
  have hmy : ∀ y, uMat m *ᵥ (uMat m⁻¹ *ᵥ y) = y := fun y => by rw [mulVec_mulVec, hmm, one_mulVec]
  have key : ∀ y, uMat (m * t * m⁻¹) *ᵥ y = uMat m *ᵥ (uMat t *ᵥ (uMat m⁻¹ *ᵥ y)) := fun y => by
    rw [hmul, hmul, mulVec_mulVec, mulVec_mulVec]
  have hs : IsSplit ε W x (m * t * m⁻¹) := by
    refine ⟨(GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem ((GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem hm ht.1) hmi,
      fun i y hy => ?_, fun y hy => ?_⟩
    · have h1 := ht.2.1 i _ (hmi _ y hy).1
      have h2 := (hm _ _ h1).1
      convert h2 using 1
      rw [key, mulVec_sub, mulVec_smul, hmy]
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [mulVec_mulVec, ← hJ, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
        exact hy _ (hm _ z hz).1
      have h2 := (hm _ _ (ht.2.2 _ hy')).1
      convert h2 using 1
      rw [key, mulVec_sub, hmy]
  have := (existsUnique_isSplit hW x).unique hs ht
  calc m * t = m * t * m⁻¹ * m := by group
    _ = t * m := by rw [this]

end GlobalTheory.RealInd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviConjugatesUnipotentRefined
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages.UnipConj

variable {n : ℕ} {ε : Fin n → Bool}

private lemma unitaryMatrix_mul_inv_eq_one (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

private lemma unitaryMatrix_inv_eq_conj_transpose (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g) * uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, unitaryMatrix_mul_inv_eq_one, Matrix.mul_one]

theorem conj_mem_flagN {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (m : Formalism.REAL.UJ ε) (hm : m ∈ flagM ε W) (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) :
    m * u * m⁻¹ ∈ flagN ε W := by
  have hmk : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i := fun i y hy => (hm i y hy).1
  have hmik : ∀ i, ∀ y ∈ W i, uMat m⁻¹ *ᵥ y ∈ W i := fun i =>
    UnipRad.inv_keeps m (W i) (hmk i)
  have key : ∀ y : Fin n → ℂ, uMat (m * u * m⁻¹) *ᵥ y - y =
      uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
    intro y
    have e := unitaryMatrix_mul_inv_eq_one m
    rw [show uMat (m * u * m⁻¹) = uMat m * uMat u * uMat m⁻¹ from rfl]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mul_assoc]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [key]
    exact hmk _ _ (hu.1 i _ (hmik _ _ hy))
  · rw [key]
    refine hmk _ _ (hu.2 _ fun x hx => ?_)
    have hx' := hmk _ x hx
    have h0 := hy _ hx'
    rw [unitaryMatrix_inv_eq_conj_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec _ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε),
      Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact h0

theorem flagN_le_refine {a b : ℕ} {W : Flag n a} {W' : Flag n b} (hW' : Monotone W')
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hp : ∀ i, W' (p i) = W i)
    (hlast : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    (g : Formalism.REAL.UJ ε) (hg : g ∈ flagN ε W) : g ∈ flagN ε W' := by
  refine ⟨fun l y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hs : l.succ ≤ p (β l).succ := by
      rw [Fin.le_def]; rw [Fin.lt_def] at h2; simp only [Fin.val_succ, Fin.coe_castSucc] at h2 ⊢; omega
    have hy' : y ∈ W (β l).succ := by rw [← hp]; exact hW' hs hy
    have := hg.1 (β l) y hy'
    rw [← hp] at this
    exact hW' h1 this
  · rw [hlast] at hy ⊢
    exact hg.2 y hy

end GlobalTheory.RealInd.Stages.UnipConj

theorem GlobalTheory.RealInd.Stages.unip_conj_refine : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W' := by
  intro n a b ε j W W' β p hW hW' hp hlast hβ m hm u hu
  exact GlobalTheory.RealInd.Stages.UnipConj.flagN_le_refine hW'.2.1 hp hlast hβ _
    (GlobalTheory.RealInd.Stages.UnipConj.conj_mem_flagN m hm u hu)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactSpanHighestWeightLine
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KSpanHighest

theorem kset_mul {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at ha hb ⊢
  exact ⟨GlobalTheory.KTypeExists.inUJ_mul ha.1 hb.1, Submonoid.mul_mem _ ha.2 hb.2⟩

theorem kset_of_mul {n : ℕ} {ε : Fin n → Bool} {k x : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε)
    (hx : Formalism.REAL.inUJ ε x) (hkx : k * x ∈ Formalism.REAL.Kset ε) : x ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at hk hkx ⊢
  refine ⟨hx, ?_⟩
  have e : x = star k * (k * x) := by
    rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hk.2, Matrix.one_mul]
  rw [e]
  exact Submonoid.mul_mem _ (Unitary.star_mem hk.2) hkx.2

theorem kspan_highest : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  intro n ε H _ _ ρ hρ hcont hiso S hfd hS Λ w hw _ hΛ hkill
  classical
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ Formalism.MainNotions.S.UJset ε := fun g hg => (Formalism.REAL.kFacts n ε).1 g hg
  let πS : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g =>
    if hg : g ∈ Formalism.REAL.Kset ε then
      LinearMap.toContinuousLinearMap ((ρ g).toLinearMap.restrict (p := S) (q := S) (fun v hv => hS g hg v hv))
    else 0
  have hπ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v : S, ((πS g v : S) : H) = ρ g v := by
    intro g hg v
    simp [πS, hg]
  have hπ0 : ∀ g, g ∉ Formalism.REAL.Kset ε → πS g = 0 := fun g hg => by simp [πS, hg]
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := by
    rw [(Formalism.REAL.kFacts n ε).2.2.2.2]
    exact ⟨by simp [Formalism.REAL.inUJ], Submonoid.one_mem _⟩
  have h1 : πS 1 = 1 := by
    ext v
    rw [hπ 1 h1K v, hρ.1]
    rfl
  have hmulK : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, πS (a * b) = (πS a).comp (πS b) := by
    intro a ha b hb
    ext v
    rw [hπ _ (kset_mul ha hb), ContinuousLinearMap.comp_apply, hπ a ha, hπ b hb, hρ.2 a (hKU a ha) b (hKU b hb)]
    rfl
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, Formalism.REAL.inUJ ε x → πS (k * x) = πS k * πS x := by
    intro k hk x hx
    by_cases hxK : x ∈ Formalism.REAL.Kset ε
    · exact hmulK k hk x hxK
    · have : k * x ∉ Formalism.REAL.Kset ε := fun h => hxK (kset_of_mul hk hx h)
      rw [hπ0 _ this, hπ0 _ hxK, mul_zero]
  have hU : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.Kset ε) πS := by
    refine ⟨⟨h1, hmulK⟩, ?_, ?_⟩
    · intro g hg v
      rw [← Submodule.norm_coe, hπ g hg v, hiso g hg, Submodule.norm_coe]
    · intro v
      have hc : ContinuousOn (fun g => ((πS g v : S) : H)) (Formalism.REAL.Kset ε) :=
        ((hcont (v : H)).mono hKU).congr fun g hg => hπ g hg v
      exact (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hc
  obtain ⟨E, hR, hUn, hder, -⟩ := ReciprocityTheory.ChartRestriction.DS.HW.uRepCompRed n ε S πS hU
  have hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inK ε Z → ∀ v : S,
      HasDerivAt (fun t : ℝ => πS (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
    intro Z hZ v
    have := hder Z hZ v
    simpa [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hwt : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Formalism.REAL.Kset ε) πS μ v ↔ IsWtOn (Formalism.REAL.Kset ε) ρ μ (v : H) :=
    fun μ v => forall₂_congr fun θ hθ => by rw [← hπ _ hθ, ← Submodule.coe_smul, Subtype.coe_inj]
  set w' : S := ⟨w, hw⟩ with hw'
  have hwE : IsWeight E Λ w' := GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ w' ((hwt Λ w').2 hΛ)
  have hhi : KHighest ε E Λ w' := by
    refine ⟨hwE, fun a b hab he => ?_⟩
    have h2 := GlobalTheory.KTypeExists.isWtOn_of_isWeightK h1 hK E hE _ _ (compact_weight_shift hR hwE he)
    have h3 : Λ + Pi.single a 1 - Pi.single b 1 = Λ + Formalism.REAL.root a b := by
      simp [Formalism.REAL.root, add_sub_assoc]
    rw [h3, hwt] at h2
    exact Subtype.ext (hkill a b hab he _ (E a b w').2 h2)
  have hst := GlobalTheory.KTypeExists.stable_of_derivedK h1 hK E hE _ (compact_span_stable (ε := ε) (F := E) w')
  have hspan : Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) ≤ (kSpan ε E w').map S.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨πS g w', hst g hg w' (mem_compact_span_self w'), hπ g hg w'⟩
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    exact GlobalTheory.KTypeExists.cdom_of_mem_kSpan E Λ μ w' y hR hUn hhi hy
      (fun h => hx0 (by rw [h]; rfl)) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE μ y ((hwt μ y).2 hxw))
  · intro x hx hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    obtain ⟨heq, hline⟩ := compact_lowering_holds S n ε E Λ w' hR hhi
    obtain ⟨c, hc⟩ := hline y (heq ▸ hy) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ y ((hwt Λ y).2 hxw))
    exact ⟨c, by rw [hc]; rfl⟩

end GlobalTheory.KSpanHighest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadicalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  first | exact @GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | exact GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | (intros; apply GlobalTheory.SeeOntoCusp.mem_NI_iff_iota <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D := by
  first | exact @GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | exact GlobalTheory.KernelSeminorm.thetaGrowth_onObjects | (intros; apply GlobalTheory.KernelSeminorm.thetaGrowth_onObjects <;> assumption)
end

