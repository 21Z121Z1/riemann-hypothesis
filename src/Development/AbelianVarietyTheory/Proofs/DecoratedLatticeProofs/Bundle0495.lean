import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0485
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TupChars

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : kˣ →* ℂˣ :=
  (Circle.toUnits.comp χ).comp (GlobalTheory.LocChar.unitsHom (ofSplit q))

theorem isComp_cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : (ofSplit q).IsComp χ (cmp q χ) := by
  intro x a ha
  have : GlobalTheory.LocChar.unitsHom (ofSplit q) x = a := Units.ext ha.symm
  simp only [cmp, MonoidHom.comp_apply, this]
  rfl

theorem cmp_apply (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) (x : kˣ) :
    ((cmp q χ x : ℂˣ) : ℂ) = (χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) : ℂ) := rfl

theorem unitsHom_int (q : GlobalTheory.FinPl.SplitPt D k) (y : kˣ) (hy : valuation k (y : k) = 1) :
    finPart D ((GlobalTheory.LocChar.unitsHom (ofSplit q) y : (AE D)ˣ) : AE D) ∈ intAE D := by
  have he1 : q.e * q.e = q.e := q.split.1
  show finPart D (q.sec y + (1 - q.e)) ∈ intAE D
  rw [(finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
  exact add_mem ((q.int_iff _).1 ((Valuation.mem_integer_iff _ _).2 hy.le))
    (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, he1])))

theorem unit_trivial (q : GlobalTheory.FinPl.SplitPt D k) {χ : (AE D)ˣ →* Circle}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ q.v) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have he1 : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hes : q.e * q.sec x = q.sec x := by
    have := q.sec_pr (q.sec x)
    rw [q.pr_sec] at this
    exact this.symm
  have hz : algebraMap (AF D.host.F) (AE D) ε * (q.sec x - q.e) = q.sec x - q.e := by
    rw [← hsum]
    linear_combination (1 - cA D q.e) * hes - he1 + (q.sec x - 1) * hec
  obtain ⟨hi, hf⟩ := (GlobalTheory.VacStabFixed.supp_iff hε _).1 hz
  have hU : ((GlobalTheory.LocChar.unitsHom (ofSplit q) x : (AE D)ˣ) : AE D) = 1 + (q.sec x - q.e) := by
    show q.sec x + (1 - q.e) = _
    ring
  refine h _ ?_ (fun w hw => ?_) (unitsHom_int q x hx) ?_
  · rw [hU, (infPart D).map_add, (infPart D).map_one, hi, add_zero]
  · rw [hU, (finPart D).map_add, (finPart D).map_one, RingHom.map_add, RingHom.map_one, hf w hw, add_zero]
  · rw [← map_inv]
    exact unitsHom_int q x⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])

theorem val_eq_one_of_sub (x : kˣ) (hx : valuation k ((x : k) - 1) < 1) : valuation k (x : k) = 1 := by
  have e : (x : k) = ((x : k) - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

end Loc

section Pack

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex}

theorem under_ne (hP : PkHyp W) (t : W.P.T) {PP P' : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (pk W).Pg) (hQ : P' ∈ (pk W).Q t) :
    P'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) := by
  intro heq
  have hL := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P' hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := (pk W).C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = (pk W).C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hmemF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    simpa using hmemE
  rw [← heq] at hmemF
  have hmemE' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P'.asIdeal := hmemF
    simpa using h2
  haveI : Finite (kP P') := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : P'.asIdeal.IsPrime := P'.isPrime
  haveI : Nontrivial (kP P') := inferInstance
  haveI : Fintype (kP P') := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP P') = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := P'.asIdeal)).2 hmemE'
    simpa using this
  have h0q : ((q : ℕ) : kP P') = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP P')
  have hd1 : ringChar (kP P') ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP P') ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP P') = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

theorem xi_charUnramAt (hP : PkHyp W) (t : W.P.T) {PP : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (pk W).Pg) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((pk W).toLevCh.xi t) (PP.under (𝓞 D.host.F)) := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
  by_contra hu
  rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
  · exact under_ne hP t hPg h hw
  · exact under_ne hP t hPg hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)

theorem eta_charUnramAt (hP : PkHyp W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (pk W).eta v := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  exact GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 ((pk W).C.isEta.unr w)

end Pack

theorem gLoc_chars : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → VTie f v → ∀ t (n : ℕ) (G : Fin n → GLoc v) pl, GRead f G pl → ∀ i, (G i).Chars (f.t t) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR _ t n G pl hG i
  have hq : (G i).q.v = (pl i).1.under (𝓞 D.host.F) := (hG.idem i).2
  have hxi : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((pk W).toLevCh.xi t) (G i).q.v := hq ▸ xi_charUnramAt hP t (pl i).2
  have heta : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (pk W).eta (G i).q.v := eta_charUnramAt hP _
  let M : ℕ → (AE D)ˣ →* Circle := (pk W).toLevCh.mu t
  let μ : ℕ → (G i).kˣ →* ℂˣ := fun m =>
    if 1 ≤ m ∧ m ≤ D.R.m then cmp (G i).q ((Lift.chrStep M (pk W).eta m).1⁻¹) else (G i).S.μ m
  have hμ : ∀ m, 1 ≤ m → m ≤ D.R.m → μ m = cmp (G i).q ((Lift.chrStep M (pk W).eta m).1⁻¹) :=
    fun m h1 h2 => if_pos ⟨h1, h2⟩
  have hunit : ∀ m (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ m x = (G i).S.μ m x := by
    intro m x hx
    by_cases hm : 1 ≤ m ∧ m ≤ D.R.m
    · rw [hμ m hm.1 hm.2]
      apply Units.ext
      rw [cmp_apply, hG.mu i m hm.1 hm.2 x (GlobalTheory.LocChar.unitsHom (ofSplit (G i).q) x) rfl]
      have hx1 := unit_trivial (G i).q hxi x hx
      have e : (Lift.chrStep M (pk W).eta m).1 = (Lift.chrStep (pk W).mu0 (pk W).eta m).1 * (pk W).toLevCh.xi t := by
        simp only [Lift.chrStep, M, LevCh.mu, Lift.tup]
        split_ifs
        · exact mul_right_comm _ _ _
        · rfl
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, e, MonoidHom.mul_apply, hx1, mul_one]
    · simp only [μ, if_neg hm]
  have htame : ∀ m, GlobalTheory.SplitWeil.IsTame (μ m) := by
    intro m x hx
    rw [hunit m x (val_eq_one_of_sub x hx)]
    exact (G i).S.tame m x hx
  have hm2 : Even D.R.m := D.R.m_even
  refine ⟨μ, htame, hunit, fun j ρ h => ?_, fun j σ h => ?_⟩
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sBF j ρ h
    have hV' : ((f.t t).sBF j ρ h).χV = M (j + 1) * (pk W).eta⁻¹ := hV
    have hW' : ((f.t t).sBF j ρ h).χW = M (j + 1) := hW
    have hodd : Odd (j + 1) := by
      obtain ⟨r, hr⟩ := hm2
      exact ⟨j / 2, by omega⟩
    have hμj : μ (j + 1) = cmp (G i).q ((M (j + 1) * (pk W).eta⁻¹)⁻¹) := by
      rw [hμ (j + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_pos hodd]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1)), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1) * (M (j + 1) * (pk W).eta⁻¹)⁻¹ = (pk W).eta := by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, unit_trivial (G i).q heta x hx, Circle.coe_one]
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sFB j σ h
    have hV' : ((f.t t).sFB j σ h).χV = M (j + 1 + 1) := hV
    have hW' : ((f.t t).sFB j σ h).χW = M (j + 1 + 1) * (pk W).eta⁻¹ := hW
    have heven : ¬ Odd (j + 1 + 1) := by
      obtain ⟨r, hr⟩ := hm2
      rw [Nat.not_odd_iff_even]
      exact ⟨j / 2 + 1, by omega⟩
    have hμj : μ (j + 1 + 1) = cmp (G i).q (M (j + 1 + 1))⁻¹ := by
      rw [hμ (j + 1 + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_neg heven]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1 + 1) * (pk W).eta⁻¹), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1 + 1) * (pk W).eta⁻¹ * (M (j + 1 + 1))⁻¹ = (pk W).eta⁻¹ := by
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    rw [e, MonoidHom.inv_apply, unit_trivial (G i).q heta x hx, inv_one, Circle.coe_one]

end GlobalTheory.TupChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalf
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem overAll_cons_iff (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι) (f f' : WO S T → ℂ) :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem sb_of_overAll (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (f : WO S T → ℂ) :
    ∀ (J : List ι) (f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ J f f' → ∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k) := by
  intro J
  induction J with
  | nil => intro _ _ i hi; simp at hi
  | cons j J ih =>
    intro f' h i hi
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ j J f f').1 h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hO.2.2.2.1
    · exact ih g hg i hi

theorem mem_latO_at_iff (p : SplitPt D k) {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (t : WO S T) (ht : IsHalf p.e t) : t ∈ latO S T LS LT (· = p.v) ↔ t ∈ latO S T LS LT fun _ => True := by
  constructor
  · intro h; exact GlobalTheory.PlaceModel.latO_le_top _ h
  · intro h
    obtain ⟨ε, hε, hsum⟩ := p.above
    have he : p.e * p.e = p.e := p.split.1
    have hεe : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, he, mul_comm (cA D p.e), p.split.2.1, add_zero]
    have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he hεe h).1
    have ht' : p.e • t = t := Matrix.ext fun i j => ht i j
    rwa [ht'] at h1

theorem isSBHalf_of_half_iff {S T : HSp D} (e : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ : WO S T → ℂ)
    (hcmp : ∀ t, IsHalf e t → (t ∈ Λ' ↔ t ∈ Λ)) (h : IsSBHalf e Λ' Φ) : IsSBHalf e Λ Φ := by
  obtain ⟨hs, K, hK, hinv, hsup⟩ := h
  refine ⟨hs, K, hK, fun u hu hh t => hinv u ((hcmp u hh).2 hu) hh t, fun t ht => (hcmp _ ?_).1 (hsup t ht)⟩
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc, mul_comm e, mul_assoc, hs t ht i j]

open Classical in
theorem datJ_nil (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (Λ : AddSubgroup (WO S T)) : datJ p α β Ψ [] = halfInd 0 Λ := by
  funext t
  have h0 : IsHalf (0 : AE D) t → t ∈ Λ := fun ht => by
    have : t = 0 := Matrix.ext fun i j => by simpa [eq_comm] using ht i j
    rw [this]; exact zero_mem _
  unfold datJ halfInd
  by_cases ht : IsHalf (0 : AE D) t
  · rw [if_pos (by simpa [eSum] using ht), if_pos ⟨h0 ht, ht⟩]; rfl
  · rw [if_neg (by simpa [eSum] using ht), if_neg fun h => ht h.2]

theorem datJ_SB (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS) (hTD : IsSelfDualC T LT)
    (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) :
    ∀ J : List ι, J.Nodup → (∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k)) →
      IsSBHalf (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil => intro _ _; rw [datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True)]; exact GlobalTheory.isSBHalf_halfInd _ _
  | cons i J ih =>
    intro hJ hSB
    rw [List.nodup_cons] at hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    rw [GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ.1 hort, eSum_cons, add_comm]
    refine GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents D S T _ _ _ _ _ (eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj) (p i).split.1
      (fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu) (ih hJ.2 fun j hj => hSB j (List.mem_cons_of_mem _ hj)) ?_
    exact isSBHalf_of_half_iff _ _ _ _ (fun t ht => mem_latO_at_iff (p i) _ _ t ht)
      (SBHalfAt.isSBHalf_extFun_latO D k (p i) S T n n' (α i) (β i) LS LT hSD hTD (Ψ i) (hSB i List.mem_cons_self))

theorem overAll_eq (ψ : AddChar (AF D.host.F) ℂ) (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS)
    (hTD : IsSelfDualC T LT) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (f : WO S T → ℂ) :
    ∀ J : List ι, J.Nodup → ∀ (f' : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) 1 f Tm →
      OverAll ψ α β LS LT Ψ J f f' → f' = Tm (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil =>
    intro _ f' Tm hTm h
    have h1 : f' = f := h
    rw [h1, datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True), ← hTm.vac, one_smul]
    rfl
  | cons i J ih =>
    intro hJ f' Tm hTm h
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ i J f f').1 h
    have hJ' := List.nodup_cons.1 hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ'.1 (h ▸ hj)
    have hmul : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj
    have hstab : ∀ u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True), (p i).e • u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True) :=
      fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu
    rw [eSum_cons, add_comm] at hTm
    have hA := GlobalTheory.T.isPlaceModel_comp_idempotentSplitTensor D ψ S T (eSum p J) (p i).e _ f Tm hmul (p i).split.1 hstab hTm
    have hg' : g = Tm (tens (p i).e (datJ p α β Ψ J) (halfInd (p i).e (latO S T (LS : Set _) (LT : Set _) fun _ => True))) :=
      ih hJ'.2 g _ hA hg
    have hSBJ := datJ_SB p α β Ψ LS LT hSD hTD horth J hJ'.2
      (sb_of_overAll ψ α β LS LT Ψ f J g hg)
    have hcmp : ∀ t, IsHalf (p i).e t → (t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ↔
        t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
      fun t ht => mem_latO_at_iff (p i) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) t ht
    have hB := GlobalTheory.T.place_model_restricted_tensor_fixed_half D ψ S T (eSum p J) (p i).e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v)) (datJ p α β Ψ J) f Tm
      hmul (p i).split.1 hstab hcmp hSBJ hTm
    rw [← hg'] at hB
    rw [hO.2.2.2.2.2 _ hB, LinearMap.comp_apply, tensR_apply, GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ'.1 hort]

theorem ratDatum_of_overAll : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (J : List ι), Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) →
    ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset →
    (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) →
    ∀ (Ψ : ι → Matrix n n' k → ℂ) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (stdHom S T) f →
    OverAll ψ α β LS LT Ψ J f f' →
    IsRatDatum ψ S T e (fun γ => (J.map fun i => Ψ i (rd (α i) (β i) (γ.map (incA D)))).prod) f f' := by
  intro D k _ _ _ _ ι p J hPl n n' _ _ _ _ ψ hψ S T α β LS LT hSD hTD hLS hLT Pset e hIdem hEq Ψ f f' hθf hvac hOver
  obtain ⟨horth, rfl⟩ := GlobalTheory.T.split_point_idempotents_orthogonal_sum_places D k ι p J _ hPl Pset e hIdem hEq
  have hΛ : stdHom S T = latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    have h1 : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext hLS
    have h2 : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext hLT
    rw [h1, h2]
  have hid := eSum_idem p horth J hPl.nodup
  unfold IsRatDatum
  rw [hΛ] at hvac ⊢
  refine ⟨datJ p α β Ψ J, datJ_SB p α β Ψ LS LT hSD hTD horth J hPl.nodup (sb_of_overAll ψ α β LS LT Ψ f J f' hOver), ?_, ?_⟩
  · intro γ
    have hh : IsHalf (eSum p J) (γ.map fun a => eSum p J * incA D a) := fun i j => by
      rw [Matrix.map_apply, ← mul_assoc, hid]
    unfold datJ
    rw [if_pos hh]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    congr 1
    unfold rd
    congr 2
    ext a b
    simp only [Matrix.map_apply, map_mul, pr_eSum p horth J hPl.nodup i hi, one_mul]
  · exact ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T LS LT hSD hTD Pset _ hIdem f hθf hvac).1,
      fun Tm hTm => overAll_eq ψ p α β Ψ LS LT hSD hTD horth f J hPl.nodup f' Tm hTm hOver⟩

end GlobalTheory.FinPl.PutIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPolesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_continuation_and_poles : GlobalTheory.Published.CuspRapidDecay → (∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (GlobalTheory.Eis.EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V (flat V a φ s₁) s₀ k) ∧ (V.rank < b → GlobalTheory.Eis.EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1)) → GlobalTheory.Published.DoublingMethod := by
  first | exact @GlobalTheory.Eis.doublingMethod_of_eisenstein | exact GlobalTheory.Eis.doublingMethod_of_eisenstein | (intros; apply GlobalTheory.Eis.doublingMethod_of_eisenstein <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLawStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) = (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.swSec_law | exact GlobalTheory.Core.Rk.SWLaw.swSec_law | (intros; apply GlobalTheory.Core.Rk.SWLaw.swSec_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

theorem rebase : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S T α β LS MS LT MT hLS hLT hMS hMT
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β
  refine ⟨fun ΛS ΛT hΛS hΛT f₀ g hg => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨-, -, hvac0, -, ⟨Tm, hTm⟩, hall⟩ := id hg
    have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' S T α β MS MT hMS hMT hU ΛS ΛT hΛS hΛT
    have hgT : g = Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v))) := by
      rw [← hE]; exact hall Tm hTm
    have hmono := sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e
        (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 g Tm := by
      refine ⟨fun Φ hΦ x hx => hTm.trans Φ (hmono Φ hΦ) x hx, fun Φ hΦ y hy => hTm.modul Φ (hmono Φ hΦ) y hy, ?_⟩
      rw [one_smul, hgT]
    have hth : IsThetaFunO ψ S T g := ((hOB LS LT hLS hLT f₀ hvac0).2.1 _ g hg).1
    have hvacg : Vac ψ S T MS MT (· = p.v) g := by
      refine ⟨hth, ?_⟩
      rw [hgT]
      exact latVac_image D k p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
    refine ⟨hvacg, fun Ψ f hf => ?_⟩
    obtain ⟨f', hf', -⟩ := (hOB MS MT hMS hMT g hvacg).1 Ψ hf.2.2.2.1
    have e1 : f' = Tm (extFun α β Ψ) := hf'.2.2.2.2.2 Tm hTm'
    have e2 : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    refine ⟨hMS, hMT, hvacg, hf.2.2.2.1, ⟨Tm, hTm'⟩, fun T' hT' => ?_⟩
    rw [e2, ← e1]
    exact hf'.2.2.2.2.2 T' hT'
  · obtain ⟨c, hc, hcomb⟩ := GlobalTheory.T.splitPlaceSchwartzBruhat_acts_as_supported_combination D k p n n' ψ hψ S T α β LS LT hLS hLT Ψ hΨ
    refine ⟨c, hc, fun f₀ hvac => ?_⟩
    obtain ⟨f, hf, -⟩ := (hOB LS LT hLS hLT f₀ hvac).1 Ψ hΨ
    exact ⟨hLS, hLT, hvac, hΨ, hf.2.2.2.2.1, fun T' hT' => (hcomb f₀ T' hT').symm⟩

end GlobalTheory.FinPl.Rebase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (Ψ : Matrix n n' k → ℂ) (c : WO S T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀)) → ∃ e : WO S T →₀ ℂ, CombAt (· = p.v) e ∧ ∀ g f, Over ψ α β LS LT g Ψ f → Vac ψ S T LS LT (· = p.v) (comb ψ S T e f) ∧ comb ψ S T c (comb ψ S T e f) = f := by
  first | exact @GlobalTheory.FinPl.DatumBack.datumBack | exact GlobalTheory.FinPl.DatumBack.datumBack | (intros; apply GlobalTheory.FinPl.DatumBack.datumBack <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  first | exact @GlobalTheory.FinPl.LineAct.line_act | exact GlobalTheory.FinPl.LineAct.line_act | (intros; apply GlobalTheory.FinPl.LineAct.line_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdBStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  first | exact @GlobalTheory.Fam.chi_zero_std | exact GlobalTheory.Fam.chi_zero_std | (intros; apply GlobalTheory.Fam.chi_zero_std <;> assumption)
end

