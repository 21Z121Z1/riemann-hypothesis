import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePart
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.BotClassDict GlobalTheory.NormSum.VacInt

variable {D : D7}

theorem idem_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D w ε') (hv : v ≠ w) : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, k1, k0⟩ := h'
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext _ fun u => ?_)
  change α u * α' u = 0
  by_cases hu : u = v
  · subst hu
    exact (congrArg (α u * ·) (k0 u hv)).trans (mul_zero _)
  · exact (congrArg (· * α' u) (h0 u hu)).trans (zero_mul _)

theorem cut_mul_cut {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {e f : R} (h : e * f = 0) (A : Matrix n n R) :
    (e • A + (1 - e • (1 : Matrix n n R))) * (f • A + (1 - f • (1 : Matrix n n R))) =
      (e + f) • A + (1 - (e + f) • (1 : Matrix n n R)) := by
  have h' : f * e = 0 := by rw [mul_comm, h]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub, smul_add,
    h, h', zero_smul, add_smul]
  abel

theorem mt_mul (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_prod (V : HSp D) (g : GA D V) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (L : List (HeightOneSpectrum (𝓞 D.host.F))) (hL : L.Nodup) :
    Formalism.L2.Theta.mt V (L.map fun v => GlobalTheory.VacStab.locPart V v g).prod =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • 1) := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, RingHom.map_zero, zero_smul, zero_smul, zero_add, sub_zero]
    rfl
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have h0 : ε v * (L.map ε).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact idem_orth (hε v) (hε w) fun e => hL.1 (e ▸ hw)
    rw [List.map_cons, List.prod_cons, mt_mul, GlobalTheory.VacStab.mt_locPart V (hε v), ih hL.2, List.map_cons, List.sum_cons,
      RingHom.map_add]
    exact cut_mul_cut (by rw [← RingHom.map_mul, h0, RingHom.map_zero]) _

theorem natCast_mem_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) : (q : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal ↔ (q : 𝓞 E) ∈ Q.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal ↔ _
  rw [map_natCast]

theorem finQ_sum_idem {q : ℕ} (hq : q.Prime) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    finQ D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (∑ v ∈ S, ε v)) = eps D.host.E fun p => p = q := by
  apply (GlobalTheory.BotFormula.toFinE D).injective
  refine FiniteAdeleRing.ext _ fun Q => ?_
  have hev : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (∑ v ∈ S, ε v).2 w = if w ∈ S then 1 else 0 := by
    intro w
    have e1 : (∑ v ∈ S, ε v).2 w = ∑ v ∈ S, evalV D.host.F w (sndA D.host.F (ε v)) := by
      rw [← map_sum, ← map_sum]
      rfl
    have e2 : ∀ v, evalV D.host.F w (sndA D.host.F (ε v)) = if w = v then 1 else 0 := by
      intro v
      obtain ⟨α, h, h1, h0⟩ := hε v
      rw [h]
      change evalV D.host.F w α = _
      split_ifs with hw
      · subst hw; exact h1
      · exact h0 w hw
    rw [e1, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_ite_eq]
  have hr : GlobalTheory.BotFormula.toFinE D (eps D.host.E fun p => p = q) Q =
      GlobalTheory.AdeleBaseChange.locMap ℚ Q (if pr (Q.under (𝓞 ℚ)) = q then 1 else 0) := by
    have := toFinE_tmul (D := D) 1 (idem fun p => p = q)
    rw [map_one, one_mul] at this
    refine (congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) this).trans ?_
    refine (GlobalTheory.AdeleBaseChange.adMap_apply _ Q).trans (congrArg _ ?_)
    rw [idem, mkInt_apply]
    congr
  have hiff : Q.under (𝓞 D.host.F) ∈ S ↔ pr (Q.under (𝓞 ℚ)) = q := by
    rw [hS, natCast_mem_under, ← Nat.prime_dvd_prime_iff_eq (pr_prime _) hq, pr_dvd_iff, natCast_mem_under]
  rw [GlobalTheory.ZeroAtPlaces.comp_base, hev, hr]
  by_cases h : Q.under (𝓞 D.host.F) ∈ S
  · rw [if_pos h, if_pos (hiff.1 h), map_one, map_one]
  · rw [if_neg h, if_neg (fun e => h (hiff.2 e)), map_zero, map_zero]

theorem exists_prod_eq_part : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  intro D V hG q hq g
  have hI : Ideal.span {(q : 𝓞 D.host.F)} ≠ ⊥ := by simpa using hq.ne_zero
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal := fun v => by
    simp [S, Ideal.dvd_span_singleton]
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine ⟨S.toList.map fun v => GlobalTheory.VacStab.locPart V v g, ?_, ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact ⟨v, ε v, hε v, (hS v).1 (Finset.mem_toList.1 hv), GlobalTheory.VacStab.suppPl_locPart V (hε v) g⟩
  · have hm := mt_prod V g ε hε S.toList (Finset.nodup_toList S)
    rw [Finset.sum_map_toList] at hm
    have he := finQ_sum_idem hq S hS ε hε
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h1 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact RingHom.map_one _
      · exact RingHom.map_zero _
    change finQ D (Formalism.L2.Theta.mt V _ i j) = eps D.host.E (fun p => p = q) * finQ D (Formalism.L2.Theta.mt V g i j) +
      (1 - eps D.host.E fun p => p = q) * (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j
    rw [hm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, he, h1, sub_mul, one_mul]

end GlobalTheory.PrimePart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory.BigTop

theorem famHyp_of_working_duty : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps),
    GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  intro 𝒜 eps Fm hW hD
  obtain ⟨⟨⟨⟨_, hDvd, _, hBox, hQD, hCYL⟩, hSm⟩, hTw⟩, hCE, hTu, hDG⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm hD
  exact ⟨h1, h2, h3, h4, h5, hDvd, hBox, hQD, hCYL, hSm, hTw, hCE, hTu, hDG⟩

end GlobalTheory.BigTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRunsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  first | exact @GlobalTheory.LevelActionOnto.levelPin_actionPin | exact GlobalTheory.LevelActionOnto.levelPin_actionPin | (intros; apply GlobalTheory.LevelActionOnto.levelPin_actionPin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩

theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentatives
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem summable_height_rpow_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD T hT g e he
  obtain ⟨m, Z, J₀, hFr⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ hD.cm n J hD.herm (r + 1) X Y hD.witt.xx hD.witt.yy hD.witt.xy
  have hinv := (GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms F E σ n J r X Y L a h hD T hT).2.2.1
  have hnn : ∀ x, 0 ≤ h x := by
    intro x
    obtain ⟨p, β, hp, k, hk, rfl⟩ := hD.iwa x
    rw [hD.ht p β hp k hk]
    exact NNReal.coe_nonneg _
  have hS := GlobalTheory.T.summable_height_rpow_parabolicCosets F E σ n J (r + 1) m X Y Z J₀ hFr L a hD.lat hD.iwa (fun x => Real.toNNReal (h x))
    (fun p β hp k hk => by simp only [hD.ht p β hp k hk, Real.toNNReal_coe]) g e (by push_cast; linarith)
  have hXinv : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hFr.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsc : ∀ p ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0), ∃ β : GL (Fin (r + 1)) (AF F ⊗[F] E), ScalesBy σ J X p β := by
    intro p hp
    obtain ⟨⟨B, -, hB⟩, B', -, hB'⟩ := hp
    have hX : adMat F X = adMat F X * (B * B') := by
      calc adMat F X = (matHom _ σ J p).1 * ((matHom _ σ J p⁻¹).1 * adMat F X) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]
        _ = adMat F X * (B * B') := by rw [hB', ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have h1 : B * B' = 1 := by
      calc B * B' = adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X * (B * B') := by rw [hXinv, Matrix.one_mul]
        _ = 1 := by rw [Matrix.mul_assoc, ← hX, hXinv]
    have h2 : B' * B = 1 := by
      first | exact mul_eq_one_comm.mp h1 | exact Matrix.mul_eq_one_comm.mp h1 | exact (Matrix.mul_eq_one_comm).1 h1 | exact Matrix.nonsing_inv_mul_cancel_left _ _ h1
    exact ⟨⟨B, B', h1, h2⟩, hB⟩
  let φ : T → GlobalTheory.Eis.Cosets (GlobalTheory.UAut.parFlag σ J X (fun _ => 0)) (ratPts σ J) := fun t =>
    GlobalTheory.AutomorphicL2Unitary.mk _ t.1
  have hrel : ∀ t : T, ∃ γ : ((GlobalTheory.UAut.parFlag σ J X (fun _ => 0)).subgroupOf (ratPts σ J)),
      (γ : ratPts σ J) * (φ t).out = t.1 :=
    fun t => GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 (Quotient.out_eq (φ t))
  have hinj : Function.Injective φ := by
    intro t t' htt
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 htt
    have hγP : ((γ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) := Subgroup.mem_subgroupOf.1 γ.2
    obtain ⟨β, hβ⟩ := hsc _ hγP
    refine Subtype.ext ((hT t'.1).unique ⟨t.2, β, ?_⟩ ⟨t'.2, 1, ?_⟩)
    · rw [← eq_mul_inv_of_mul_eq hγ]; exact hβ
    · simp [ScalesBy]
  refine (hS.comp_injective hinj).congr fun t => ?_
  obtain ⟨γ, hγ⟩ := hrel t
  have hγP : ((γ⁻¹ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) :=
    Subgroup.mem_subgroupOf.1 (inv_mem γ.2)
  obtain ⟨β, hβ⟩ := hsc _ hγP
  have hout : ((φ t).out : ratPts σ J) = γ⁻¹ * t.1 := eq_inv_mul_of_mul_eq hγ
  simp only [Function.comp, Real.coe_toNNReal _ (hnn _)]
  rw [hout, Subgroup.coe_mul, mul_assoc]
  refine congrArg (· ^ e) (hinv _ ⟨?_, β, Subgroup.mem_top _, ?_⟩ _)
  · exact SetLike.coe_mem _
  · exact hβ

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverseStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) (ν : Formalism.L2.Host.HChar D.host.E),
  IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) → ChrEq χ ν := by
  first | exact @GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | exact GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | (intros; apply GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLe
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isKC_Eab_of_posC {p q : ℕ} {c d : Ix p q} (h : posC c d) : IsKC (Eab c d) := by
  intro a b hab
  have hcd : sameBlock c d := by
    cases c <;> cases d <;> simp_all [posC, sameBlock]
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1
    exact absurd hcd hab
  · rfl

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem isKC_Eab_diag {p q : ℕ} (c : Ix p q) : IsKC (Eab c c) := by
  intro a b hab
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    exact absurd (sameBlock_refl _) hab
  · rfl

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ c, act (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → act (Eab c d) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem hw_sup_le (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hG : Good act) (N N' : Submodule ℂ V) (hN : KStable act N) (hN' : KStable act N') (μ : Ix p q → ℚ) :
    (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  intro v hv
  obtain ⟨hvs, hvh⟩ := Submodule.mem_inf.1 hv
  obtain ⟨n, hn, n', hn', rfl⟩ := Submodule.mem_sup.1 hvs
  rw [mem_hwSub_iff] at hvh
  obtain ⟨hw, hpos⟩ := hvh
  have hI : KStable act (N ⊓ N') := fun X hX w hw' =>
    Submodule.mem_inf.2 ⟨hN X hX w (Submodule.mem_inf.1 hw').1, hN' X hX w (Submodule.mem_inf.1 hw').2⟩
  have h1 : ∀ c, act (Eab c c) n - ((μ c : ℚ) : ℂ) • n ∈ N ⊓ N' := by
    intro c
    refine Submodule.mem_inf.2 ⟨N.sub_mem (hN _ (isKC_Eab_diag c) n hn) (N.smul_mem _ hn), ?_⟩
    have e : act (Eab c c) n - ((μ c : ℚ) : ℂ) • n = -(act (Eab c c) n' - ((μ c : ℚ) : ℂ) • n') := by
      have := hw c
      rw [map_add, smul_add] at this
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    rw [e]
    exact N'.neg_mem (N'.sub_mem (hN' _ (isKC_Eab_diag c) n' hn') (N'.smul_mem _ hn'))
  have h2 : ∀ c d, posC c d → act (Eab c d) n ∈ N ⊓ N' := by
    intro c d hcd
    refine Submodule.mem_inf.2 ⟨hN _ (isKC_Eab_of_posC hcd) n hn, ?_⟩
    have e : act (Eab c d) n = -(act (Eab c d) n') := by
      have := hpos c d hcd
      rw [map_add] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [e]
    exact N'.neg_mem (hN' _ (isKC_Eab_of_posC hcd) n' hn')
  obtain ⟨n1, hn1N, hn1h, hd⟩ := GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG (N ⊓ N') N hI hN μ n hn h1 h2
  have hdN' : n + n' - n1 ∈ N' := by
    have : n + n' - n1 = (n - n1) + n' := by abel
    rw [this]
    exact N'.add_mem (Submodule.mem_inf.1 hd).2 hn'
  have hvH : n + n' ∈ hwSub act μ := (mem_hwSub_iff act μ _).2 ⟨hw, hpos⟩
  have : n + n' = n1 + (n + n' - n1) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hn1N, hn1h⟩)
    (Submodule.mem_inf.2 ⟨hdN', (hwSub act μ).sub_mem hvH hn1h⟩)

example : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ μ : Ix p q → ℚ, (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := hw_sup_le

end GlobalTheory.HoweR
end

