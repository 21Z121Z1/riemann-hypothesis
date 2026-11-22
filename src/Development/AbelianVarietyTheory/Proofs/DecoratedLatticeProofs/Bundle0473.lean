import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStageTrivialTwist
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.RedAt

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq

theorem val_lt_of_pr {y : D.host.E} (hy : valuation K (q.pr (incA D y)) < 1) : PP.valuation D.host.E y < 1 := by
  by_cases hle : PP.valuation D.host.E y ≤ 1
  · obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hle
    have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
      le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q hq _).1 h'))
    have hr : r ∈ PP.asIdeal := by
      refine (LevelTest.val_lt_one_iff q hq r).1 ?_
      rw [show ((r : 𝓞 D.host.E) : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd,
        mul_one]
      exact hy
    have hdv : PP.valuation D.host.E ((d : 𝓞 D.host.E) : D.host.E) = 1 :=
      le_antisymm (PP.valuation_le_one _) (not_lt.1 fun h' => d.2 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 h'))
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).2 hr
    rw [← e, map_mul] at h1
    rwa [show algebraMap (𝓞 D.host.E) D.host.E (d : 𝓞 D.host.E) = ((d : 𝓞 D.host.E) : D.host.E) from rfl, hdv, mul_one] at h1
  · exfalso
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hle (by simp)
    have h1 : PP.valuation D.host.E y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hle)
    have h2 := GlobalTheory.SeeSaw.LevChi.val_rat_lt q hq h1
    have h3 : q.pr (incA D y) * q.pr (incA D y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
    have h4 := congrArg (valuation K) h3
    rw [map_mul, map_one] at h4
    have h5 : valuation K (q.pr (incA D y)) * valuation K (q.pr (incA D y⁻¹)) < 1 :=
      (mul_le_of_le_one_right' h2.le).trans_lt hy
    exact (ne_of_lt h5) h4

theorem hasRes_of_pr {z : AE D} (c : 𝓞 D.host.E) (hz : valuation K (q.pr z - q.pr (incA D (c : D.host.E))) < 1) :
    GlobalTheory.Mem.Col2.HasRes PP (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z)) (Ideal.Quotient.mk PP.asIdeal c) := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : Valued.v (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) < 1 := by
    rw [← GlobalTheory.Mem.Col2.adAt_inclE D.host.F, ← map_sub, e, add_sub_cancel_left]
    exact valued_nat_mul_lt hr hN'
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    refine GlobalTheory.SeeSaw.LevChi.val_pr_lt q hq ?_
    have e2 : toEAf D (z - incA D y) = toEAf D z - Formalism.UG.inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y := by
      rw [RingHom.map_sub]
      rfl
    rw [e2, map_sub, GlobalTheory.Mem.Col2.adAt_inclE]
    exact h1
  have h3 : valuation K (q.pr (incA D (y - (c : D.host.E)))) < 1 := by
    have e3 : q.pr (incA D (y - (c : D.host.E))) = (q.pr z - q.pr (incA D (c : D.host.E))) - q.pr (z - incA D y) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [e3]
    exact Valuation.map_sub_lt _ hz h2
  have h4 := val_lt_of_pr q hq h3
  refine ⟨c, rfl, ?_⟩
  have e4 : GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
      (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) +
        algebraMap D.host.E (PP.adicCompletion D.host.E) (y - (c : D.host.E)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [e4]
  refine Valuation.map_add_lt _ h1 ?_
  rw [valued_algebraMap]
  exact h4

end Split

end GlobalTheory.FamTrace.RedAt

namespace GlobalTheory.FamTrace.RedAt

set_option maxHeartbeats 1000000 in

theorem inJ_red : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy i v i0 h hv hM
  have hstd := hA.tr.std.some u
  obtain ⟨w, hw, ρ, hu, hres⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (F0 W u).gl hstd.gl.piG i0 v h
  have hid := (ha.tie row col).2.idem i
  have hPg : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hwe : w = (a.pl i).1 := GlobalTheory.Mem.Col2.TC.GLev0.vGs_inj (X := X) hPg
    (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩) (hu.trans (hv.symm.trans hid.2))
  subst hwe
  have hn : (I.rec7 l Z).R.N 0 = (I.rec7 l Z).R.k := by simp [Ranks.N]
  have hr := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  have key : ∀ r c : Fin ((I.rec7 l Z).R.N 0), c ≤ r →
      Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1)) r c =
        if r = c then 1 else 0 := by
    intro r c hcr
    obtain ⟨r', rfl⟩ : ∃ r', r = finCongr hr r' := ⟨(finCongr hr).symm r, by simp⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = finCongr hr c' := ⟨(finCongr hr).symm c, by simp⟩
    have hcr' : c' ≤ r' := hcr
    have hsm := (hM r' c').2 hcr'
    have hinj : (finCongr hr r' = finCongr hr c') ↔ r' = c' := (finCongr hr).injective.eq_iff
    have e1 : (a.G i).q.pr (incA (I.rec7 l Z) (((if r' = c' then 1 else 0 : 𝓞 (I.rec7 l Z).host.E)) : (I.rec7 l Z).host.E)) =
        (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r' c' := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hR := hasRes_of_pr (a.G i).q hid.1 (z := mt ((I.rec7 l Z).sp.X 0) κ r' c') (if r' = c' then 1 else 0) (by
      rw [e1]
      exact hsm)
    have hyrc : y.1.1 (finCongr hr r') (finCongr hr c') = toEAf (I.rec7 l Z) (mt ((I.rec7 l Z).sp.X 0) κ r' c') := by
      rw [← hy]
      rfl
    rw [← hyrc] at hR
    obtain ⟨hh, e⟩ := hres _ _ hR
    rw [GlobalTheory.Mem.Col2.TC.GLev0.mat_one]
    unfold Formalism.L2.Forms.redM
    refine (dif_pos hh).trans (e.trans ?_)
    by_cases hrc : r' = c'
    · subst hrc
      rw [if_pos rfl, if_pos rfl, map_one]
      exact map_one ρ
    · rw [if_neg hrc, if_neg (fun e => hrc (hinj.1 e)), map_zero]
      exact map_zero ρ
  have hlt : ∀ x : Fin ((I.rec7 l Z).R.N 0), (x : ℕ) < (I.rec7 l Z).R.k := fun x => hn ▸ x.2
  have hb : ∀ x : Fin ((I.rec7 l Z).R.N 0), Formalism.L2.Forms.blkOf (I.rec7 l Z).R.k (I.rec7 l Z).R.t x = x :=
    fun x => if_pos (hlt x)
  refine ⟨fun x z hxz => ?_, fun x _ => ?_, fun x z hz => absurd hz (ne_of_lt z.2), fun h' => absurd h' (by simp)⟩
  · rw [hb, hb] at hxz
    rw [key x z (le_of_lt (show z < x from hxz)), if_neg (fun e => by subst e; exact lt_irrefl _ hxz)]
  · rw [key x x le_rfl, if_pos rfl]

end GlobalTheory.FamTrace.RedAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceFwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hint : ∀ a b, valuation k (g.val a b) ≤ 1)
    (h : ∀ a b, e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) : g ∈ colGroup k κ (Fin τ) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  let M : Matrix (XIx (Fin κ) (Fin τ) 0) (XIx (Fin κ) (Fin τ) 0) 𝒪[k] := Matrix.of fun a b => ⟨g.val a b, hint a b⟩
  have hM : ∀ a b, e b ≤ e a → (residue 𝒪[k]).mapMatrix M a b = (1 : Matrix _ _ 𝓀[k]) a b := fun a b hab => by
    have h1 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
      simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
    rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ?_
    convert h a b hab using 2
    simp only [M, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hdet : ((residue 𝒪[k]).mapMatrix M).det = 1 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Matrix.submatrix_apply, hM _ _ le_rfl, Matrix.one_apply_eq]
    · intro i j hij
      have hij' : j < i := hij
      rw [Matrix.submatrix_apply, hM _ _ (by simpa using hij'.le), Matrix.one_apply_ne (e.symm.injective.ne hij'.ne')]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← residue_ne_zero_iff_isUnit, RingHom.map_det, hdet]
    exact one_ne_zero
  refine ⟨_, ⟨hu.unit, Units.ext ?_, rfl⟩, fun a b hab => ?_⟩
  · ext a b
    rfl
  · rw [hp, hp] at hab
    exact hM a b hab

theorem embX_mem {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : g ∈ colGroup k κ (Fin τ)) :
    embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  exact (h2 g hg).1

set_option maxHeartbeats 1000000 in

theorem colGroup_of_red {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : GL (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A.1)
    (hU : A ∈ Formalism.L2.Col.uniUT n _ κ []) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : (mt V x).map q.pr = F.β * g.val * F.γ) : g ∈ colGroup k κ (Fin τ) := by
  subst hr
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  refine mem_colGroup e he g (fun a b => ?_) fun a b hab => ?_
  · have := (valuation k).map_add_le (hM (e a) (e b)).le (LevelTest.val_le_one q (R (e a) (e b)))
    rwa [sub_add_cancel, ← hgM] at this
  · obtain ⟨-, h1, h2⟩ := Formalism.L2.Col.mem_uniUT.1 hU
    have ha : (e a).val < κ := hn ▸ (e a).2
    rcases hab.eq_or_lt with h | h
    · obtain rfl : b = a := e.injective h
      have h3 : R (e b) (e b) - 1 ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq, hR, h2 _ ha, map_one]
      have := (valuation k).map_add_lt (hM (e b) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [← hgM] at this
      simpa using this
    · have h3 : R (e a) (e b) ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hR, h1 _ _ ha h]
      have := (valuation k).map_add_lt (hM (e a) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [sub_add_cancel, ← hgM] at this
      rwa [Matrix.one_apply_ne (fun h' : a = b => h.ne' (congrArg e h')), sub_zero]

end Loc

theorem exists_red {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad) {y : (I.stp u I.mu0 0).Cl → TC.GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → TC.GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k) (x : S.U)
    (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ A : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.asIdeal), A ∈ Formalism.L2.Col.uniUT (B.R.N 0) _ B.R.k [] ∧ LevRead.IsRed w x.1 A.1 := by
  subst hJ
  obtain ⟨h, h1, h2, -⟩ := TC.GLev0.chi_prod I S hR hI x
  exact ⟨_, inv_mem (h1 ⟨w, hw⟩), h2 ⟨w, hw⟩⟩

set_option maxHeartbeats 1000000 in

theorem traceAtG_of_mem : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → GlobalTheory.FamTrace.TraceAtG a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ κ _ y hκy hy i g hg
  obtain ⟨hS⟩ := hA.tr.std
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨k₀, hR⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨A, hU, hA'⟩ := exists_red I hA.tr.ok ((TC.spaces_in_coordinates I hA.tr.ok hP l Z).2.2.2 0 (Nat.zero_le _)).1
    ((W.R.T.cols.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev hR ⟨_, hy⟩ (a.pl i).1 ((hA.lev.2.1 _).1 (a.pl i).2)
  letI := (a.G i).fld; letI := (a.G i).val; letI := (a.G i).top; letI := (a.G i).loc
  exact embX_mem (a.G i).S g (colGroup_of_red (a.G i).q ((ha.tie row col).2.idem i).1 ((I.rec7 l Z).sp.X 0)
    (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (show B.R.N 0 = B.R.k by simp [Ranks.N]) _
    ((ha.stdG i).1 0 (Nat.zero_le _)) hκy hA' hU g hg)

end GlobalTheory.FamTrace.TraceFwd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.IdemSplitTw

theorem idem_eq_add_twist : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∃ e₀ : AE (I.rec7 l Z), IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs) ∧ J.A.e = e₀ + ∑ i, (J.G i).q.e := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ
  have hI : I.Ok := hW.tr.ok
  have hPr := l.pr
  have hd : Disjoint ((B.primes X).vT u) (Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup (W.P.I.tup t))) :=
    Finset.disjoint_left.2 fun P h1 h2 =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr hI.sel_ok (hPr.T_prime u) (hI.T_mem u) (hPr.T_ne_g u) h2
        (GlobalTheory.Mem.Col2.T_mem_vT hPr u ⟨P, h1⟩)
  have hgq : Disjoint (B.primes X).vGs
      (Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)) :=
    GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup (W.P.I.tup t)) hPr hI.sel_ok hI.g_mem
  have hid := hJ.is.idem
  have hS : Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup (W.P.I.tup t)) u =
      ((B.primes X).vT u ∪ (B.primes X).vGs) ∪
        Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
    simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Finset.union_assoc]
  rw [hS] at hid
  have hsp : GlobalTheory.ExportSeries.SplitSet (D := I.rec7 l Z) _ := ⟨_, hid⟩
  have hdisj : Disjoint ((B.primes X).vT u ∪ (B.primes X).vGs)
      (Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)) :=
    Finset.disjoint_union_left.2 ⟨hd.mono_right Finset.subset_union_right, hgq⟩
  have h0 := (hsp.mono Finset.subset_union_left).isIdemSum
  refine ⟨_, h0, ?_⟩
  rw [GlobalTheory.IdemSumAdd.idemSum_union _ _ _ _ _ GlobalTheory.ExportSeries.idemAt hdisj
    (fun PP hPP => hsp.isIdemAt (Finset.mem_union_right _ hPP)) h0 hid]
  congr 1
  have himg : Finset.univ.image J.pl =
      Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
    ext PP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (hW.tq.Q t _).1 (J.mem i)
    · intro h
      exact hJ.surj PP ((hW.tq.Q t PP).2 h)
  rw [← himg, Finset.sum_image fun i _ j _ e => hJ.inj e]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.ExportSeries.idemAt_eq (J.G i).idem

end GlobalTheory.Fam.IdemSplitTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw

theorem stepLam_of_ns : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  intro D h1 h2 h3 h4 h5 h6 h7 h8
  intro hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' m X hX mR hmR φ v hv H₀ hH₀ hκ B hB u₁ hu hq
  obtain ⟨H, -, hH, -, hL, hol⟩ := h7 c hw.com B hB k hk
  obtain ⟨r1, -, r2, r3⟩ := h8 hG c w hw k hk s s' hs hs' p hp
  have hinv := GlobalTheory.ChainTw.invFam_bounded D c w hw k hk.le s hs u₁ B hu hB
  have hns := GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams D c hw.com c.S subset_rfl B hB hinv k hk
  have hKF : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hv.1, rfl⟩
  have ex := fun u₂ => h6 hG c w hw k hk s s' hs hs' p hp ipD ip hM m X hX mR hmR φ v hv u₁ u₂ _ hu hq hns _ hol
  simp only [GlobalTheory.ChainTw.Check.const_eq w k p m X mR φ v _ H H₀ (r1 H H₀ hH hH₀) r2 r3] at ex
  have hne : p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) ≠ 0 := fun h0 => by
    have e := ex u₁
    rw [h0] at e
    have z : s'.pet 0 0 = 0 := by simp [PiLocalization₂.pet, Lift.pet]
    rw [z] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exact mul_ne_zero hκ hL ((map_eq_zero _).1 e)
    · have := hM.pos u₁ hu.1
      rw [e] at this
      simp at this
  obtain ⟨v1, v2⟩ := h5 hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ _ hKF
  obtain ⟨w₀, hw0, hadj⟩ := v1 ⟨u₁, hne⟩
  refine ⟨w₀, hw0, hadj, fun x₁ hx₁ => ?_⟩
  have e1 := v2 w₀ hadj u₁ x₁ hx₁
  refine ⟨?_, ?_, fun u₂ x₂ hx₂ => ?_⟩
  · exact (h1 c w hw (k + 1) hk s' hs').2.2.2 x₁ w₀ _ (e1 ▸ hne) (e1 ▸ h2 hG c w hw k hk s s' hs hs' p hp u₁ _ φ hu _ hKF hne)
  · exact (h4 c w hw (k + 1) hk s' hs').1 x₁ w₀ (e1 ▸ hne) (e1 ▸ h3 hG c w hw k hk s s' hs hs' p hp u₁ φ hq _ hKF)
  · have e := ex u₂
    rw [e1, v2 w₀ hadj u₂ x₂ hx₂] at e
    rw [← e]
    exact (hM'.schur x₁ x₂ w₀ w₀).symm

end GlobalTheory.ChainTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTraceChiCol

open Classical in

def colLam {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : ℂ :=
  if h : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal then
    Formalism.L2.Forms.lamJ (T.gl.psi0 h.choose v h.choose_spec) (T.gl.chiB h.choose v h.choose_spec) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
        (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g)))
  else 1

theorem type_idx_unique {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {j j' : Fin 2}
    (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal) : j' = j := by
  by_contra hne
  have hg : D.host.g j' ≠ D.host.g j := by
    intro e
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      subst hj hj' <;> first | exact hne rfl | exact D.host.g_ne e | exact D.host.g_ne e.symm
  have hc : Nat.Coprime (D.host.g j') (D.host.g j) := (Nat.coprime_primes (D.host.g_prime j') (D.host.g_prime j)).2 hg
  obtain ⟨a, b, hab⟩ : IsCoprime (D.host.g j' : ℤ) (D.host.g j : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (1 : 𝓞 D.host.F) ∈ v.asIdeal := by
    have e : ((a * (D.host.g j' : ℤ) + b * (D.host.g j : ℤ) : ℤ) : 𝓞 D.host.F) = 1 := by rw [hab]; simp
    rw [← e]
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h') (v.asIdeal.mul_mem_left _ h)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem colLam_eq {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)}
    (j : Fin 2) (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal)
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    colLam T v g = Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
  have hex : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := ⟨j, h⟩
  unfold colLam
  rw [dif_pos hex]
  have key : ∀ (j' : Fin 2) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal), j' = j →
      Formalism.L2.Forms.lamJ (T.gl.psi0 j' v h') (T.gl.chiB j' v h') D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j' v h' (T.glev0.fr j' v h') (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) =
      Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
    rintro j' h' rfl; rfl
  exact key _ _ (type_idx_unique h hex.choose_spec)

end GlobalTheory.FamTraceChiCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesDisjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DisjProof

theorem vT_disjoint_vGs : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end

