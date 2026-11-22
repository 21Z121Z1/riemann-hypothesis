import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0547
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0546
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0488
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0542
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem GlobalTheory.FamTrace.uloc_T_of_inLevG : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FamTrace.InLevG a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (F0 W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hF := hA.tr.std.some u
  have hI := hA.tr.ok
  have hP := hA.tr.pins.some
  obtain ⟨kk, R⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have hlb := R.lb ()
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s (W.R.T.cols.forms u).atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact (W.R.T.cols.forms u).atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : (F0 W u).cls0.lev.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N 0) ((((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ (W.R.T.cols.forms u).atT.piU hp0 _ ?_
    rw [hF.piU]; exact hlb
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) := by
    have h1 := hPr.piT_cop u
    have e : s (W.R.T.cols.forms u).atT.piU = B.fields.conjO ((B.primes X).piT u) := by
      apply RingOfIntegers.ext (K := (I.rec7 l Z).host.E)
      rw [hsc, hF.piU]
      exact (B.fields_conjO_coe _).symm
    rw [e, hF.piU]
    exact h1
  have hint : ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r t : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) w (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r t) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E w :=
    GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice (I.rec7 l Z) ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (a.g.x 0).L
      ((hat.std.2 0 (Nat.zero_le _)).1) κ hIn.1
  refine GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime (Formalism.L2.Forms.sigD (I.rec7 l Z)) (fun x => star_star x) hgram (F0 W u).cls0.lev (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) rfl hpq hcop hTp.ne_zero hL v hv _ (GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2) ?_ ?_
  · intro r t
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 r t) ∈ _
    rw [← hy]
    exact hint v r t
  · intro t
    obtain ⟨c, hc, he⟩ := GlobalTheory.T.true_geometry_character W hA u a ha hat κ hκ hIn.2.1 hint v hv t
    refine ⟨c, hc, ?_⟩
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 _ t) - _ = _
    rw [← hy, he, hF.piU]
    rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevOnto

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

theorem map_pr_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : (mt V g).map q'.pr = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  obtain ⟨ε', hε', hE'⟩ := q'.above
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε] at hE
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε'] at hE'
  have hsp := q'.split
  have h0 : q'.e * (q.e + cA D q.e) = 0 := by
    have h1 : q'.e = q'.e * (q'.e + cA D q'.e) := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
    rw [h1, mul_assoc, hE', hE, ← map_mul, GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ (Ne.symm hv), map_zero, mul_zero]
  have hpr : q'.pr (q.e + cA D q.e) = 0 := by
    rw [← q'.pr_sec (q'.pr _), q'.sec_pr, h0, map_zero]
  ext a b
  rw [Matrix.map_apply]
  have h2 : mt V g a b = (mt V g - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h2, map_add, ← hg a b, map_mul, hpr, zero_mul, zero_add]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem locHom_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {Y : Type} [Fintype Y] [DecidableEq Y]
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (F : Frame k' V.rank Y) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : GlobalTheory.LevIdx.locHom q' V F g = 1 := by
  refine ((GlobalTheory.LevIdx.eq_locHom_iff q' V F g 1).1 ?_).symm
  rw [map_pr_eq_one q q' V g hg hv, Units.val_one, Matrix.mul_one, F.βγ]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

theorem same_pl (hW : AllTrue W) (ha : a.Is) (hTr : a.True) {t t₂ : W.P.T} (J : QJ a t) (hJ : J.Reads) (J₂ : QJ a t₂)
    (hJ₂ : J₂.Reads) (i : Fin J.r) (i₂ : Fin J₂.r) (h : (J.G i).q.v = (J₂.G i₂).q.v) : J.pl i = J₂.pl i₂ := by
  have h1 := (GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t J hJ).2 i
  have h2 := (GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t₂ J₂ hJ₂).2 i₂
  exact hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t₂, J₂.mem i₂⟩ (h1.symm.trans (h.trans h2))

theorem locHom_gl (j : ℕ) {PP} (h₁ h₂ : QAll W PP) (hj₁ : j ≤ (a.Q PP h₁).s + 1) (hj₂ : j ≤ (a.Q PP h₂).s + 1)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (a.Q PP h₂).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, (mt _ (gl y)).map (a.Q PP h₂).q.pr = ((a.Q PP h₂).FX j hj₂).β * y.val * ((a.Q PP h₂).FX j hj₂).γ) (y) :
    GlobalTheory.LevIdx.locHom (a.Q PP h₁).q _ ((a.Q PP h₁).FX j hj₁) (gl y) = y :=
  ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y)).symm

end GlobalTheory.LevOnto
end

namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

theorem mem_relax (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t₂ : W.P.T} (J : QJ a t) (hJ : J.Reads)
    (α : J.Ch j) (J₂ : QJ a t₂) (hJ₂ : J₂.Reads) (i : Fin J₂.r)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr =
      ((J₂.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J₂ i hj; omega)).β * y.val * ((J₂.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J₂ i hj; omega)).γ)
    (y) (hy : y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) : gl y ∈ GlobalTheory.LevProd.relax J j hj α := by
  have hAt : ∀ P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop, P (J₂.G i).q.v → gl y ∈ GlobalTheory.FinPl.grpAt _ P :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt (· = (J₂.G i).q.v) rfl)⟩, ?_⟩
  · by_cases hv : GlobalTheory.LevProd.twAt J (J₂.G i).q.v
    · exact Subgroup.mem_sup_right (hAt _ hv)
    · exact Subgroup.mem_sup_left (GlobalTheory.T.true_geometry_lattice_open W hW u a ha hTr j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy)
  · rw [Subgroup.mem_comap, Subgroup.mem_pi]
    intro i' _
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl y) ∈ KO (J.G i').k _
    by_cases hv : (J.G i').q.v = (J₂.G i).q.v
    · have e := same_pl hW ha hTr J hJ J₂ hJ₂ i' i hv
      have key : ∀ P (hP : P ∈ (pk W).Q t) (hj₁ : j ≤ (a.Q P ⟨t, hP⟩).s + 1), P = J₂.pl i →
          GlobalTheory.LevIdx.locHom (a.Q P ⟨t, hP⟩).q _ ((a.Q P ⟨t, hP⟩).FX j hj₁) (gl y) ∈ KO (a.Q P ⟨t, hP⟩).k
            (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) := by
        rintro P hP hj₁ rfl
        rw [locHom_gl j _ _ hj₁ _ gl (fun y => (hgl y).2) y]
        exact hy
      exact key _ (J.mem i') _ e
    · rw [locHom_eq_one (J₂.G i).q (J.G i').q _ _ (gl y) (hgl y).1 (Ne.symm hv)]
      exact one_mem _

theorem onto : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ GlobalTheory.LevProd.Up a j hj, GlobalTheory.LevProd.phi J j hj g = x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α x hx
  have hex : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  have hUp : GlobalTheory.LevProd.Up a j hj = GlobalTheory.LevProd.relax hex.choose_spec.choose j hj hex.choose_spec.choose_spec.2.some := by
    unfold GlobalTheory.LevProd.Up
    rw [dif_pos hex]
  have hJ₀ : hex.choose_spec.choose.Reads := hex.choose_spec.choose_spec.1
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J i hj; omega))
  choose gl _ hglp _ using hgl
  refine ⟨((List.finRange J.r).map fun i => gl i (x i)).prod, ?_, ?_⟩
  · rw [hUp]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact mem_relax hW ha hTr j hj _ hJ₀ _ J hJ i (gl i) (hglp i) (x i) (hx i)
  · rw [map_list_prod, List.map_map]
    have hphi : ∀ i, GlobalTheory.LevProd.phi J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
      intro i
      funext i'
      show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
      by_cases h : i' = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
      · rw [Pi.mulSingle_eq_of_ne h]
        refine locHom_eq_one (J.G i).q (J.G i').q _ _ _ (hglp i (x i)).1 fun hv => h ?_
        exact hJ.inj (same_pl hW ha hTr J hJ J hJ i' i hv.symm)
    simp only [Function.comp_def, hphi]
    exact list_prod_mulSingle x

end GlobalTheory.LevOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.AtG

set_option maxHeartbeats 1000000 in

theorem mem_Uloc_badG : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FamTrace.InLevG a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (F0 W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hstd := hA.tr.std.some u
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 2, ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
    rcases hv with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨w, hw, -, hu, -⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (F0 W u).gl hstd.gl.piG i0 v hi0
  have hwP : w ∈ (pk W).Pg := (hA.lev.2.1 w).2 (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩)
  obtain ⟨i, hi⟩ := a.pl.surjective ⟨w, hwP⟩
  have hqv : (a.G i).q.v = v := by
    rw [((ha.tie row col).2.idem i).2, hi]
    exact hu
  have hTv : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    GlobalTheory.Mem.Col2.TC.GLev0.T_notMem X u i0 hi0
  have hx := GlobalTheory.T.true_geometry_compact_level_property W hA u a hat κ hκ y hy hIn.1 v hTv
  have hfr : (F0 W u).glev0.fr i0 v hi0 = 1 := hstd.fr0 i0 v hi0
  refine ((F0 W u).glev0.mem i0 v hi0 _ hx).2 ?_
  rw [hfr]
  exact GlobalTheory.T.true_geometry_final_index W hA u a ha hat row col hc κ hκ y hy i v i0 hi0 hqv (GlobalTheory.T.true_geometry_final_measure W hA u a ha hat κ hIn.2.2 i)

end GlobalTheory.FamTrace.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinGrp

open GlobalTheory.FinPl

theorem map_ofFn_prod_eq {G M : Type*} [Group G] [Monoid M] (φ : G →* M) :
    ∀ {r : ℕ} (a : Fin r → G) (i : Fin r), (∀ j, j ≠ i → φ (a j) = 1) → φ (List.ofFn a).prod = φ (a i)
  | 0, _, i, _ => i.elim0
  | r + 1, a, i, h => by
    rw [List.ofFn_succ, List.prod_cons, map_mul]
    by_cases hi : i = 0
    · subst hi
      have h1 : φ (List.ofFn fun j : Fin r => a j.succ).prod = 1 := by
        rw [map_list_prod]
        refine List.prod_eq_one fun x hx => ?_
        rw [List.map_ofFn, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact map_ofFn_prod_eq φ (fun j => a j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

variable {D : D7}

theorem loc_facts {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (i : Fin F.r) :
    GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) ∧
    IsCompact (GlobalTheory.QuotientFiniteLevel.locK F j σ h i : Set (GA D (c.V (j + 1)))) ∧
    IsOpen {x : grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) |
      (x : GA D (c.V (j + 1))) ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i} := by
  have hd : j + 1 + ((F.Q i).s - j) = (F.Q i).s + 1 := by have := (F.Q i).hs; omega
  obtain ⟨hce, hrange, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1))
    ((F.Q i).X (j + 1) ⊕ Fin ((F.Q i).s - j)) ((F.Q i).FY (j + 1) ((F.Q i).s - j) hd)
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ((F.Q i).gl_loc _ _ hd)
  have hr : ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd).range =
      grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) := by
    rw [hrange]; congr 1; funext p; exact propext Finset.mem_singleton.symm
  obtain ⟨hJo, hJc, -⟩ := (F.Q i).reg.2.2 (j + 1) ((F.Q i).s - j) hd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr]; intro x hx; obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx; exact ⟨g, rfl⟩
  · rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.coe_map]; exact hJc.image hce.continuous
  · obtain ⟨U, hU, hUe⟩ := hce.isInducing.isOpen_iff.1 hJo
    convert hU.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨g, rfl⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.mem_map]
    constructor
    · rintro ⟨g', hg', e⟩
      have : g' ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hUe.symm ▸ hg'
      rw [← e]; exact this
    · intro hU'
      have hg : g ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hU'
      rw [hUe] at hg
      exact ⟨g, hg, rfl⟩

theorem qK_grp : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w →
    ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧
      IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧
      IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) :
        Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  intro D c v t w F hF j σ h
  have hloc := loc_facts F j σ h
  have hv : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have hle : ∀ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := fun i => (hloc i).1.trans
    (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp => (Finset.mem_singleton.1 hp) ▸ hv i)
  have hoff : ∀ i i', i ≠ i' →
      GlobalTheory.QuotientFiniteLevel.locK F j σ h i' ≤ grpAt (c.V (j + 1)) (· ∉ ({(F.Q i).q.v} : Finset (Pl D))) := fun i i' hii' =>
    (hloc i').1.trans (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp hp' =>
      hii' (hF.inj ((Finset.mem_singleton.1 hp').symm.trans (Finset.mem_singleton.1 hp))))
  have hcomm : Pairwise fun i i' => ∀ x y : GA D (c.V (j + 1)),
      x ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i → y ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i' → Commute x y := by
    intro i i' hii' x y hx hy
    exact (GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) {(F.Q i).q.v}).2.2.2.2.1 x ((hloc i).1 hx) y (hoff i i' hii' hy)
  have hqK : GlobalTheory.QuotientFiniteLevel.qK F j σ h = ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i := rfl
  have hQle : GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := iSup_le hle
  refine ⟨hQle, ?_, ?_⟩
  · have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hcont : Continuous (Subgroup.noncommPiCoprod hcomm) := by
      have e : ⇑(Subgroup.noncommPiCoprod hcomm) = fun x =>
          ((List.finRange F.r).map fun i => ((x i : GlobalTheory.QuotientFiniteLevel.locK F j σ h i) : GA D (c.V (j + 1)))).prod := by
        funext x
        simp [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod, Finset.noncommProd, List.ofFn_eq_map]
      rw [e]
      exact continuous_list_prod _ fun i _ => continuous_subtype_val.comp (continuous_apply i)
    haveI : ∀ i, CompactSpace (GlobalTheory.QuotientFiniteLevel.locK F j σ h i) := fun i => isCompact_iff_compactSpace.1 (hloc i).2.1
    have : (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) = Set.range (Subgroup.noncommPiCoprod hcomm) := by
      rw [hqK, ← hrange, MonoidHom.coe_range]
    rw [this]; exact isCompact_range hcont
  · set V := c.V (j + 1) with hVdef
    set K := GlobalTheory.QuotientFiniteLevel.locK F j σ h with hKdef
    obtain ⟨-, -, hQf, -, -, ⟨eQ, heQ⟩, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V w.Q
    have hbot : ∀ a, a ∈ grpAt V (· ∈ w.Q) → a ∈ grpAt V (· ∉ w.Q) → a = 1 := by
      intro a h1 h2
      have : eQ (⟨a, h1⟩, 1) = eQ (1, ⟨a, h2⟩) := by
        apply Subtype.ext; rw [heQ, heQ]; simp
      exact congrArg (fun p => (p.1 : GA D V)) (eQ.injective this)
    choose e he using fun i => (GlobalTheory.FinPl.SetCut.grp_split D V {(F.Q i).q.v}).2.2.2.2.2.1
    have he' : ∀ i (z : GfC V), (z : GA D V) = (((e i).symm z).1 : GA D V) * (((e i).symm z).2 : GA D V) := by
      intro i z; rw [← he i, Homeomorph.apply_symm_apply]
    let ι : grpAt V (· ∈ w.Q) → GfC V := fun x => ⟨x.1, hQf x.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let U : Set (grpAt V (· ∈ w.Q)) := ⋂ i, {x | ((((e i).symm (ι x)).1 : _) : GA D V) ∈ K i}
    have hUo : IsOpen U := isOpen_iInter_of_finite fun i =>
      (hloc i).2.2.preimage (continuous_fst.comp ((e i).symm.continuous.comp hι))
    have h1U : (1 : grpAt V (· ∈ w.Q)) ∈ U := by
      refine Set.mem_iInter.2 fun i => ?_
      have : (e i).symm (ι 1) = 1 := by
        rw [Homeomorph.symm_apply_eq]; apply Subtype.ext; rw [he]; simp [ι]
      show ((((e i).symm (ι 1)).1 : _) : GA D V) ∈ K i
      rw [this]; exact (K i).one_mem
    have hprj : ∀ i, ∀ b ∈ grpAt V (· ∉ ({(F.Q i).q.v} : Finset (Pl D))),
        GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v b = 1 := fun i b hb =>
      ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ b).1 hb).2 _ (by simp)
    have hUsub : U ⊆ (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (grpAt V (· ∈ w.Q)) : Subgroup _) : Set _) := by
      intro x hx
      have hx' := Set.mem_iInter.1 hx
      let a : Fin F.r → GA D V := fun i => (((e i).symm (ι x)).1 : GA D V)
      have ha : ∀ i, a i ∈ K i := fun i => hx' i
      have hp : (List.ofFn a).prod ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h := by
        refine Subgroup.list_prod_mem _ fun y hy => ?_
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (le_iSup K i) (ha i)
      have hy1 : ∀ i, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v ((x : GA D V) * ((List.ofFn a).prod)⁻¹) = 1 := by
        intro i
        have hxi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (x : GA D V) =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) := by
          have := he' i (ι x)
          change (x : GA D V) = a i * _ at this
          rw [this, map_mul, hprj i _ (((e i).symm (ι x)).2).2, mul_one]
        have hpi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (List.ofFn a).prod =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) :=
          map_ofFn_prod_eq _ a i fun j' hj' => hprj i _ (hoff i j' (Ne.symm hj') (ha j'))
        rw [map_mul, map_inv, hxi, hpi, mul_inv_cancel]
      have hyQ : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∈ w.Q) :=
        mul_mem x.2 (inv_mem (hQle hp))
      have hyN : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∉ w.Q) := by
        refine (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ _).2 ⟨hQf hyQ, fun p hp' => ?_⟩
        obtain ⟨i, rfl⟩ := (hF.places p).1 (not_not.1 hp')
        exact hy1 i
      have hxp : (x : GA D V) = (List.ofFn a).prod := mul_inv_eq_one.1 (hbot _ hyQ hyN)
      show (x : GA D V) ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h
      rw [hxp]; exact hp
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds h1U) hUsub)

end GlobalTheory.QFinGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  first | exact @GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | exact GlobalTheory.UnitLevelInt.entry_mem_of_levelVL | (intros; apply GlobalTheory.UnitLevelInt.entry_mem_of_levelVL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelSection

theorem fock_mem_degenerate : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) := by
  intro D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp a ha g
    exact GlobalTheory.StdUnn.SiegelLaw.value_zero_parabolic D n V ψ χ θ μ ω hω Φ p hp a ha g
  · exact GlobalTheory.T.continuous_weilSchrodinger_standardUnn_eval_zero D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω Φ
  · have hfin := GlobalTheory.T.fockVector_schrodingerModel_isKFinite D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
    let L : schwartzA θ V.rank n →ₗ[ℂ] (G D n → ℂ) :=
      { toFun := fun Ψ g => (ω g Ψ).1 0
        map_add' := fun Ψ₁ Ψ₂ => by funext g; simp
        map_smul' := fun c Ψ => by funext g; simp }
    rw [isKFinite_iff]
    refine ⟨(Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}).map L, inferInstance, ?_⟩
    intro k hk
    have e : (fun g : G D n => (ω (g * k) Φ).1 0) = L (ω k Φ) := by
      funext g; simp [L, map_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.StdUnn.SiegelSection
end

