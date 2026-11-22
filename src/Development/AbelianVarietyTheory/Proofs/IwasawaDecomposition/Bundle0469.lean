import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.Chart0

open GlobalTheory.Mem.Col2.MemChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

abbrev lvQ (a : I.ι) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

def yT (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) : GA B (B.R.N 0) :=
  Classical.epsilon fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)

theorem yT_spec (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    PtOf (yT I u a c * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a 0).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1))
    ⟨g * (kStd X u (B.R.N 0))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem cos0 {u : B.Word} {a : I.ι} (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ (by have := B.R.two_le_m; omega)] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem stepZero_classes_bijective_decoratedLattice (hI : I.Ok) (u : B.Word) (a : I.ι) :
    Function.Bijective fun c : (I.stp u a 0).Cl =>
      decoCls (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ((I.stp u a 0).rep c).1.1.deco := by
  letI := StepZero.idxUnique (hI.idx_ok a)
  have h := StepZero.clMap_bijective (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)) (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) (StepZero.levQAt_zero (I.Tp a) (hI.idx_ok a))
  convert h using 1
  funext c
  have e := StepZero.clMap_cl (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) c.1 ((I.stp u a 0).rep c)
  have e2 : (I.stp u a 0).cl c.1 ((I.stp u a 0).rep c) = c := by
    obtain ⟨b, q⟩ := c
    exact congrArg (Sigma.mk b) ((I.stp u a 0).rp_spec b q)
  rw [e2] at e
  exact e.symm

theorem stab_range0 (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (stM (lvG I a) (lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c).range ↔
      ∃ g : UF B.fields.E (B.R.N 0) × (colLev I.Ch 0).grp, ufGL B.fields.E (B.R.N 0) g.1 = γ ∧
        g • ((I.stp u a 0).rep c).1.1.deco = ((I.stp u a 0).rep c).1.1.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) ((I.Tp a).pref u 0) (StepZero.levGAt_zero (I.Tp a) hL) c.1 g, rfl, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) _ (StepZero.levGAt_zero (I.Tp a) hL) c.1 g _).symm.trans (congrArg (fun q => q.1.1.deco) hg)
  · rintro ⟨g₀, rfl, hg⟩
    obtain ⟨g, h1, h2⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy (StepZero.levGAt_zero (I.Tp a) hL)
      (StepZero.levQAt_zero (I.Tp a) hL) c.1 _ _ g₀ hg
    exact ⟨⟨g, h2⟩, congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h1⟩

theorem red0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u), redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)

theorem lev0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q) :
    x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, cos0 I _ _⟩
    · show ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := red0 I hI hPr u a c x κ h1 (h2 ▸ h)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = colLev I.Ch 0 → ∀ g : Λ'.grp,
        g.1 ∈ (colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

theorem chr0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (hxU : x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp)
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ((levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) ⟨x, hxU⟩ : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a 0).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩ = (⟨κ.2.1.1, hΛ c.1 ▸ κ.2.1.2⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((lvG I a c.1).chr κ.2.1 * (lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

set_option maxHeartbeats 1000000 in

theorem charts_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  intro B X I hI hP l Z u a
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  refine ⟨badG (I.rec7 l Z), Unit, chOf, fun _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)

end GlobalTheory.Mem.Col2.TC.Chart0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullHermitianColumnsTrueColumns
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mem_integralNormOne_of_normOneDetClass_eq_one (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (h : u1Dt H SQ x = 1) :
    x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H) := by
  obtain ⟨a, ha⟩ := exists_lift H x
  have e : (QuotientGroup.mk a : DtQ H SQ) = 1 := (normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha).symm.trans h
  have ha' : a ∈ KDq H SQ := (QuotientGroup.eq_one_iff a).1 e
  refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).2 fun w => ?_
  exact (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).1 (Subgroup.mem_sup_left (KDq_le_KD H SQ ha')) w (conjPrime₂ w)
    ((isConjPl_iff H w _).2 rfl)

theorem unitIdeleImage_eq_map_integralNormOne : UOQ H SQ = ((Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)).subgroupOf (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))).map (u1Dt H SQ) := by
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_of_idele H a
    refine ⟨x, ?_, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩
    refine (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a hx).2 fun w => ?_
    exact (ha w).trans (ha (conjPrime₂ w)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_lift H x
    rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, mk_mem_UOQ, KDq_sup_unitIdl]
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H a).2 fun w w' hw => ?_
    rw [(isConjPl_iff H w w').1 hw]
    exact (GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq R H x a ha).1 hx w

end Gen

section Main

open Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem detPt_of_reads (hI : I.Ok) (u : B.Word) (i : ℕ) {Ch : Type} {chOf : (I.stp u I.mu0 i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u I.mu0 i chOf Lb U chi y st k) (c : (I.stp u I.mu0 i).Cl)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det (y c)) :
    detPt B.host I.SQ ((I.stp u I.mu0 i).rep c).1.1 = u1Dt B.host I.SQ x := by
  obtain ⟨p, hp, hN⟩ := hR.k_std (chOf c)
  refine GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level B.R B.host _ _ _ _ I.SQ _ (y c) (k (chOf c)) x (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni
    (hN ▸ hp.lat) (fun P hP => ?_) hx
  refine hR.k_off _ _ (GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes B X I hI u P hP) ?_ (Or.inl rfl)
  rintro ⟨Q, hQ, -⟩
  rw [GlobalTheory.T.q_mu0_eq_empty B X I] at hQ
  exact absurd hQ (Finset.notMem_empty Q)

theorem det_reGL {a b : ℕ} (h : a = b) {A : Type} [CommRing A] (g : GL (Fin a) A) :
    Matrix.GeneralLinearGroup.det (reGL h A g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  refine Units.ext ?_
  simp [reGL, Matrix.GeneralLinearGroup.det]

variable (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : ColsTiedSym (I.rec7 l Z))

include I in

theorem det_normOne_classStepZero_trueColumns (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (c : ((I.rec7 l Z).mem u).C.cls 0)
    (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det ((C.herm.base.lev0 u).y c).1) :
    (I.rec7 l Z).detCls u 0 c = u1Dt B.host I.SQ x := by
  obtain ⟨k, hk⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  refine detPt_of_reads I hI u 0 hk c x ?_
  have e := (C.car0 u).y_eq c
  rw [hx]
  exact (e ▸ det_reGL _ _).symm

include I in

theorem detI_std (hI : I.Ok) (hS : I.StdC l Z C) (u : B.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ B.R.m)
    (c : ((I.rec7 l Z).mem u).C.cls i) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData B.R B.host))
    (hx : Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det
      ((C.herm.base.cls u i h1 hm (C.herm.base.chOf u i c)).y ⟨c, rfl⟩).1) :
    (I.rec7 l Z).detCls u i c = u1Dt B.host I.SQ x := by
  by_cases h2 : i + 1 ≤ B.R.m
  · obtain ⟨k, hk⟩ := (hS u).mid i h1 h2
    refine detPt_of_reads I hI u i hk c x ?_
    have e := (C.carC u i h1 h2 (C.herm.base.chOf u i c)).y_eq ⟨c, rfl⟩
    rw [hx]
    exact (e ▸ det_reGL _ _).symm
  · obtain rfl : i = B.R.m := by omega
    obtain ⟨k, hk⟩ := (hS u).ends B.R.m le_rfl (Or.inr rfl)
    refine detPt_of_reads I hI u _ hk c x ?_
    have e := (C.carM u).y_eq c
    have key : ∀ (β : C.herm.base.Ch u B.R.m) (hb : C.herm.base.chOf u B.R.m c = β),
        Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm β).y ⟨c, hb⟩).1 =
          Matrix.GeneralLinearGroup.det ((C.herm.base.cls u B.R.m h1 hm (C.herm.base.chOf u B.R.m c)).y ⟨c, rfl⟩).1 := by
      rintro _ rfl
      rfl
    rw [hx, ← key _ (chOf_m C.herm.base u c)]
    exact (e ▸ det_reGL _ _).symm

def hermS (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricHermitianColumns (I.rec7 l Z) :=
  { C.herm.base with
    dt := u1Dt B.host I.SQ
    dt_surj := normOneFiniteAdeleDetClass_surjective B.host I.SQ
    dt_ker := mem_integralNormOne_of_normOneDetClass_eq_one B.host I.SQ
    dt_open := GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass B.R B.host _ I.SQ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1
    dt_UO := unitIdeleImage_eq_map_integralNormOne B.host I.SQ
    dt_rat := fun z x h => GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class B.R B.host I.SQ z x h
    det0 := fun u c x h => det_normOne_classStepZero_trueColumns I l Z C hI hS u c x h
    detI := fun u i h1 hm c x h => detI_std I l Z C hI hS u i h1 hm c x h }

theorem relDet_std (hI : I.Ok) (hS : I.StdC l Z C) : Formalism.L2.Herm.SymmetricRelativeDeterminant (I.rec7 l Z) (hermS I l Z C hI hS) := by
  intro N L L' g _ hg x hx
  obtain ⟨idl, hp⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by ext t; exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩) (fun _ => rfl)
    (fun N L L' t h => h)
  exact GlobalTheory.Mem.NormOneIdeal.relDet_eq_of_pinned (I.rec7 l Z) idl hp _ (hermS I l Z C hI hS).dt (hermS I l Z C hI hS).dt_ker
    (hermS I l Z C hI hS).dt_UO (hermS I l Z C hI hS).dt_rat L L' g x hg hx

theorem exists_colsFullS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (C : ColsTiedSym (I.rec7 l Z)) (g : Formalism.L2.Herm.SymmetricGroupCompatibility (I.rec7 l Z) C.herm.base), I.StdC l Z C → Formalism.L2.Herm.VolumeCompatible (I.rec7 l Z) → ∃ Fu : ColsFullS C, HEq Fu.1.g g ∧ I.StdDt l Z Fu.1.base.dt := by
  intro B X I hI _ l Z C g hS hV
  let Fu : Formalism.L2.Herm.FullTiedS (I.rec7 l Z) :=
    { base := hermS I l Z C hI hS
      atT := C.herm.atT
      vol := hV
      levelZeroCompatibility := C.herm.levelZeroCompatibility
      g := g
      ad := C.herm.ad
      cof := C.herm.cof
      piG := C.herm.piG
      stabMap := C.herm.stabMap
      fvI := C.herm.fvI
      relDet := relDet_std I l Z C hI hS
      std := C.herm.std
      vpos := B.V_pos
      baseL := C.herm.baseL }
  refine ⟨⟨Fu, rfl⟩, HEq.rfl, ?_⟩
  intro x a ha
  exact normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha

end Main

end GlobalTheory.Mem.Col2.FullDt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  first | exact @GlobalTheory.Mem.LiftModG.exists_lift_mod_g | exact GlobalTheory.Mem.LiftModG.exists_lift_mod_g | (intros; apply GlobalTheory.Mem.LiftModG.exists_lift_mod_g <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContextsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsLayeredData_of_goodScaleContexts : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  first | exact @GlobalTheory.Fc.recExP_of_recAtG | exact GlobalTheory.Fc.recExP_of_recAtG | (intros; apply GlobalTheory.Fc.recExP_of_recAtG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepChartsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberStep_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), I.ReadsK l Z u I.mu0 i hi chOf K ∧ (∀ c, ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧ ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.exists_charts | exact GlobalTheory.Mem.Col2.MemChart.exists_charts | (intros; apply GlobalTheory.Mem.Col2.MemChart.exists_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1StandardStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ptOf_mul_K1_standard : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | exact GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | (intros; apply GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatumStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  first | exact @GlobalTheory.TrueTheta.exists_family_of_curve | exact GlobalTheory.TrueTheta.exists_family_of_curve | (intros; apply GlobalTheory.TrueTheta.exists_family_of_curve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime : ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Coprime p q → ∀ T : ℤ, Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) = ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) * ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  first | exact @GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | exact GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | (intros; apply GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_symVec_sub_ite_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg a j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 a).2.1
    · exact ((X.weightVectorsIntegral _).2.2 a).2.2.2
  refine wInt_of_zmod X k hg ?_
  have ha := a.2
  have hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1 := rfl
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1]
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2
    rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm] at h
    by_cases e : j = GlobalTheory.Mem.SymChar.Resid.posE D a
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))),
        map_zero] at h
  rw [dif_neg h1]
  have hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a := fun e => by
    have := congrArg Fin.val e; rw [hpos] at this; omega
  rw [if_neg hne, sub_zero]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2]; exact hW _
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4]; exact (X.formsAtZero.2 a).2
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3]; exact (X.gramIntegral a _).2.1
  · rw [dif_neg h3, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_e0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.hA_e0_symVec | exact GlobalTheory.Mem.SymChar.hA_e0_symVec | (intros; apply GlobalTheory.Mem.SymChar.hA_e0_symVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | exact GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt <;> assumption)
end

