import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfGammaLemmas
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

theorem lemmaGD_cc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (hg : Good K 1 LL) :
    ∃ cc : ℤ → ↥(OL LL), ∀ x : ℤ, (-(((P.PD K).p : ℕ) : ↥(OL LL))) * cc x =
      ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) - 1 := by
  obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (H := H) hg
  have hne : (z : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  let I : Ideal ℤ_[l] := Ideal.span {((l : ℕ) : ℤ_[l])}
  have hI : (z : ℤ_[l]) - 1 ∈ I := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by omega)
    simpa using this
  have hz1 : Units.map (Ideal.Quotient.mk I).toMonoidHom z = 1 := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_one]
    exact (Ideal.Quotient.eq.2 hI).trans (map_one _)
  have hw : ∀ x : ℤ, ∃ w : ℤ_[l], -((l : ℕ) : ℤ_[l]) * w = ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    intro x
    have h1 : (Ideal.Quotient.mk I) ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) = (Ideal.Quotient.mk I) 1 := by
      have := congrArg Units.val
        (show Units.map (Ideal.Quotient.mk I).toMonoidHom (z ^ (-x)) = 1 by
          rw [map_zpow, hz1, one_zpow])
      rw [Units.coe_map, Units.val_one] at this
      exact this.trans (map_one _).symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    exact ⟨-w, by rw [← hw]; ring⟩
  choose w hw using hw
  refine ⟨fun x => algebraMap ℤ_[l] ↥(OL LL) (w x), fun x => ?_⟩
  have e := congrArg (algebraMap ℤ_[l] ↥(OL LL)) (hw x)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at e
  rw [P.PD_p K, e]
  congr 1
  have hzu : Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom z =
      (H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam := Units.ext hz
  rw [← hzu, ← map_zpow]
  rfl

theorem lemGB_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ) (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg)) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGB ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hQ := hA.2.2.2.2.2.2.2.2.2.2.2.2.1 l K LL hg
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  refine lemGB_of _ hQ (fun hCA => Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA)
    (hC4 l K 1 LL hg) h9 (Formalism.MainNotions.LiftingTheory.lattice_clause_every_situation D HW F l K 1 LL hg)
    (fun _ => lemmaGD_cc (HW l) hg) (fun _ => ?_) (h56 l K LL hg)
  rw [(D.loc l).PD_p K]
  exact Formalism.MainNotions.UnusedSlot80.Split2.isUnit_pred l LL

theorem lemmaGs_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ)
    (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg))
    (hGA : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGA ((HW l).W K 1 LL hg)) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemmaGs ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  exact lemmaGs_of_lemGAB _ (hGA l K LL hg)
    (lemGB_L D HW F Cm CR CA CB CK C₀ hA hC4 h56 l K LL hg)

theorem local_clause_of_gamma_lemmas (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ)
    (hA : Formalism.MainNotions.CrystallineLiftingInputs.admitted D HW F Cm CR CA CB CK C₀) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (h56 : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], WachGammaDerivation ((HW l).W K 1 LL hg))
    (hGA : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemGA ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm18 D HW F Cm := by
  intro l _ K LL hg _
  exact lemmaG_of_sharp _ (lemmaGs_L D HW F Cm CR CA CB CK C₀ hA hC4 h56 hGA l K LL hg)

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

def CoordSteps (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (C₀ : Coord W (baseIdOf hR) W.one)
      (_h : CoordHom C₁ C₂ F) (e₀ : C₀.V), ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e

def ArcSteps (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (hC : CoordHom C₁ C₂ F),
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (hCu : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      ∀ c ∈ (cutsOf hCu).cuts,
        ∃ (κ₁ κ₂ : PowerSeries O) (r₁ r₂ : ℕ) (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
          (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
          (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ((cutsOf hCu).ell c)
            (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p (E.HArc (gPar Gp S η) Gp S η (kdOf ty) (bbOf ty) c)
              ((cutsOf hCu).ell c)) κ₁ (lamOf C₁ c ((cutsOf hCu).ell c) e₁))
          (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ((cutsOf hCu).ell c)
            (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p (E.HArc (gPar Gp S η) Gp S η (kdOf ty) (bbOf ty) c)
              ((cutsOf hCu).ell c)) κ₂ (lamOf C₂ c ((cutsOf hCu).ell c) e₂))
          (Mh : MapHyp hR uZ ιZ F c),
          (∀ ϖ : O, Irreducible ϖ →
            LevSteps Hy₁ ϖ j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) Gp S η
                (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₁ ∧
            LevSteps Hy₂ ϖ j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) Gp S η
                (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₂) ∧
          MapSteps hC Hy₁ Hy₂ Mh j (E.parM (baseIdOf hR).Bs.ℓ h (gPar Gp S η)) (gPar Gp S η) η
            (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e₁ e₂ P

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G PowerSeries IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem ringSteps_of [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (η : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (hℓ2 : PD.p ≠ 2) (hℓm : (PD.p : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G1 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ X = (1 + X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL, 1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL)
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a) :
    (lvModel Hy f' kind b η).K1b ∧ (lvModel Hy f' kind b η).HasU (W.χΓ W.gam) ∧
      (∀ s < ell, ((lvModel Hy f' kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s ∧
        ((lvModel Hy f' kind b η).lev s).PhiGammaCommute) ∧
      (lvModel Hy f' kind b η).UnitsAt ∧ (lvModel Hy f' kind b η).Compl ϖ := by
  obtain ⟨w, hw⟩ := G1
  exact LevelStatements.Link.linkRing LevelStatements.Lv.rhoUnique LevelStatements.Lv.splitCompl LevelStatements.Lv.cycloSimple
    LevelStatements.Lv.psCoprime LevelStatements.Lv.rhoUnit LevelStatements.Lv.descendDvd LevelStatements.Lv.piSeries ϖ hϖ
    (lvData Hy f' kind b η) (hℓ := ⟨PD.hp⟩) hℓ2 hℓm n0 hn0 hroot (baseIdOf hR).ι w hw W.φ₀ hφ
    (baseIdOf hR).ι_φ LevelStatements.Lv.psCyclo G2 (rhoZ W c) hρζ (lvModel Hy f' kind b η)
    (fun s _ a ζ => map_eval_rhoL hR c s a ζ) (W.χΓ W.gam) (uZ : ℤ_[PD.p]) huZ ιZ hutie
    (fun _ _ => rfl)
    (fun s _ f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)
    (fun j => (j.1 : ℤ_[PD.p]))
    (fun j => (by simpa using congrArg (fun x : ℤ_[PD.p]ˣ => (x : ℤ_[PD.p])) j.2 :
      ((j.1 : ℤ_[PD.p])) ^ (PD.p - 1) = 1))
    hom'
    (fun s _ j f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

theorem univStep_of (hL : UnivLinkStep) (hd : DvdStep) (hR : InvLiftStep) (hC : ClassMapStep)
    (hH : FrameStep) (hM : ModelFStep) (hU1 : FirstFrameHypothesis) (hk : KapPiStep) (hU2 : SecondPropositionHypothesis)
    (hD : DownSlotHypothesis) (hUp : UpSlotHypothesis) (hMx : MixedSlotHypothesis) : UnivStep :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) (hM D HW F Cm CA CB CK hA) (hU1 D HW F Cm CA CB CK hA)
      (hk D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA) (hD D HW F Cm CA CB CK hA)
      (hUp D HW F Cm CA CB CK hA) (hMx D HW F Cm CA CB CK hA)

theorem local_theorem_of_all_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep) (hM : ModelFStep)
    (hU1 : FirstFrameHypothesis) (hkp : KapPiStep) (hU2 : SecondPropositionHypothesis) (hD : DownSlotHypothesis) (hUp : UpSlotHypothesis)
    (hMx : MixedSlotHypothesis) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_lemma_properties hG hL hd hq hn h9 he hw hk hl hg hf hγ ho
    (univStep_of hUL hd hR hC hH hM hU1 hkp hU2 hD hUp hMx)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

open Classical in

def SecondPropositionRingInput (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Prop :=
  IsUnit (algebraMap (LetA O n) W.EE π') ∧ IsUnit (algebraMap (LetA O n) W.EE Eπ) ∧
  (∃ g ∈ W.AΔ, W.γA W.gamK π' = π' * g) ∧
  ∃ ν ∈ W.AΔ, ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h' ∧
  ∃ (N : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O),
    (∀ k, f k ∈ W.AΔ) ∧
    (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h')) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) ∧
    ((Finset.range N).filter fun k => cc k = 1).card ≤ finrank K₀ K + 1

end Local

def secondPropositionRingAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, SecondPropositionRingInput ((HW l).W K 1 LL hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRingHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → secondPropositionRingAll D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def DownSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → DownSlotProposition D HW

def UpSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → UpSlotProposition D HW

def MixedSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → modelFR D HW → MixedSlotProposition D HW

end Formalism.MainNotions.N.Ln34

end
end

