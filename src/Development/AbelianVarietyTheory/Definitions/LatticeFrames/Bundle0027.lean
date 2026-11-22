import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteOfPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.PlacesTest

variable {D : D7}

theorem exists_one_place (D : D7) (Z : Finset (Pl D)) : ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)),
    v ∉ Z ∧ Places (fun _ : Unit => p) [()] (· = v) := by
  have h := ((GlobalTheory.FinPl.AlmostAll.latA_eq_latV D).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    (GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹))).and Z.eventually_cofinite_notMem
  obtain ⟨v, ⟨e, ε, he, hε, hs⟩, ⟨h1, h2, h3⟩, hZ⟩ :=
    ((Set.infinite_iff_frequently_cofinite.1 (infinite_splitIdem_places D)).and_eventually h).exists
  obtain ⟨p, -, hp⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  refine ⟨v, p, hZ, by simp, by simp, fun _ _ _ => rfl, fun x => by simp [hp], fun _ => ?_⟩
  unfold SplitPt.UnitAA
  rw [hp]
  exact ⟨fun a ha => ⟨h2 a ha, h3 a ha⟩, h1⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem finite_of_places {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) : {x | P x}.Finite := by
  have : Finite ι := Set.finite_univ_iff.1 ((List.finite_toSet I).subset fun i _ => h.all i)
  exact (Set.finite_range fun i => (p i).v).subset fun x hx => by
    obtain ⟨i, rfl⟩ := (h.mem x).1 hx
    exact ⟨i, rfl⟩

theorem not_places_of_eq {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} {i j : ι} (hij : i ≠ j) (hv : (p i).v = (p j).v) :
    ¬ Places p I P := fun h => hij (h.inj hv)

theorem places_empty (p : Empty → SplitPt D k) : Places p [] fun _ => False :=
  ⟨List.nodup_nil, fun i => i.elim, fun i => i.elim, fun _ => ⟨False.elim, fun ⟨i, _⟩ => i.elim⟩, fun i => i.elim⟩

variable {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S} {LT : Lat T}

theorem reps_nil (Ψ : ι → Matrix n n' k → ℂ) (P : Pl D → Prop) : Reps ψ α β LS LT Ψ [] P (Finsupp.single 0 1) :=
  ⟨OffTest.combAt_single_zero P 1, fun f _ => OffTest.comb_single_zero ψ S T f⟩

theorem vac_zero (P : Pl D → Prop) : Vac ψ S T LS LT P 0 := by
  have h : ∀ u, heisO ψ S T u 0 = 0 := fun u => by funext w; simp [heisO]
  exact ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => h u⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩,
    fun u _ => h _, fun _ _ u _ _ => h u⟩

theorem sb_of_reps {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {I : List ι} {P : Pl D → Prop} {c : WO S T →₀ ℂ}
    (h : Reps ψ α β LS LT Ψ (i :: I) P c) : Ψ i ∈ SB (Matrix n n' k) ∧ IsSelfDualC S LS ∧ IsSelfDualC T LT := by
  obtain ⟨g, -, h1, h2, -, h3, -⟩ := h.2 0 (vac_zero P)
  exact ⟨h3, h1, h2⟩

end

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (x y : WO S L'') :
    symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := by
  have := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) (by simpa using hτ) x y
  simp only [symplOH, kap, this]
  simp

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (x y : WO S L'') :
    kap τ S (x + y) = kap τ S x + kap τ S y := by
  simp only [kap, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.mul_add, adj_add, Matrix.add_mul, smul_add]

theorem lastBi_heis (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (a : WO A S) (x : WO S X) (Ξ Φ₂) (u v) :
    heisO ψ A S a (fun u' => heisO ψ S X x (lastBi o o'' τ Ξ Φ₂ u') v) u =
      lastBi o o'' τ (heisO ψ V₀ S ((o.resS S).symm (a, kap τ S (o''.resT S x).2)) Ξ) (heisO ψ S T (o''.resT S x).1 Φ₂) u v := by
  simp only [heisO, lastBi, OrthDec.boxT, map_add, Prod.fst_add, Prod.snd_add, kap_add]
  rw [o.symplOH_resS, o''.symplOH_resT, ← map_add (o.resS S).symm]
  simp only [AddEquiv.apply_symm_apply, symplOH_kap τ hτ, AddChar.map_add_eq_mul, Prod.mk_add_mk]
  ring

theorem smallPair_zero {V₀ A L S T : HSp D} (o : OrthDec V₀ A L) (om₁ : Om V₀ S) (omT : Om S T) (vA : Vol A) (vS : Vol S)
    (vT : Vol T) (Ξ Φ₂ F) : smallPair o om₁ omT vA vS vT 0 Ξ Φ₂ F = 0 := by
  simp [smallPair, liftA]

theorem smallPair_eq_Q {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {B : BesLev D 0} (t : Last ψ T B) (o : OrthDec B.V B.A B.L)
    (ho : ∀ a, o.emb (a, 1) = embA B.d B.o a) (φ Φ₁ Φ₂ F) :
    smallPair o t.s.om t.om B.vA t.s.vW t.vT φ Φ₁ Φ₂ F = t.Q φ Φ₁ Φ₂ F := by
  have h0 : (o.resS t.J.W).symm (0, 0) = 0 := map_zero (o.resS t.J.W).symm
  simp only [smallPair, liftA, Last.Q, ho, h0]

end GlobalTheory.FinPl.PlacesTest

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def OneOn (S : Set ℝ) (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u

def OneAllOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).nzSet) ≤ gamL D large₂.sc.L C * ddC X Y u u

def OneAll : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      HD D L C' Cl Cg cb Cu cT CT → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).nzSet) ≤ gamL D L C * ddC X Y u u

def SDiagOn (S : Set ℝ) (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → TrueS D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def GamRange (D : D7) (L : ℝ) : Prop :=
  (D.R.m : ℝ) ^ 5 * D.R.f * L ≤ Real.log (AdmissibleBoundsFromSource.Gam D) ∧ 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k

def SDiagAtLed (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), (∃ large₂ : SizeData₂ D, large₂.sc.L = L) → GamRange D L → TrueS D → HD D L C' Cl Cg cb Cu cT CT →
      ∀ u, SDiagAt D u (gamL D L CD) c

def SDiagG (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), GamRange D L → TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

theorem pow_five_mul_f_pos (D : D7) : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f := by
  have hf : 0 < D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  positivity

theorem gamRange_iff {D : D7} (large₂ : SizeData₂ D) :
    GamRange D large₂.sc.L ↔ 1 ≤ large₂.CGam ∧ 8 * large₂.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ D.R.k := by
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hp : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := mul_pos (pow_five_mul_f_pos D) (by linarith)
  have hG : Real.log (AdmissibleBoundsFromSource.Gam D) = large₂.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
    unfold AdmissibleBoundsFromSource.Gam; rw [large₂.Gam_eq D.u₀]; ring
  unfold GamRange
  rw [hG, le_mul_iff_one_le_left hp, mul_assoc 8]

theorem gammaRange_of_sizeHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ large₂.CGam)
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : GamRange D large₂.sc.L := by
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hp : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := mul_pos (pow_five_mul_f_pos D) (by linarith)
  have h8 : 8 * large₂.CGam ≤ C' := h.1
  have hk : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := h.2.1
  refine (gamRange_iff large₂).2 ⟨h1, ?_⟩
  have := mul_le_mul_of_nonneg_right h8 hp.le
  linarith

theorem dataNW_of_window {D : D7} {C0 : ℝ} (h3 : 1 ≤ C0) (hd : StandingNumericalData D C0) : GlobalTheory.Core.Deg.DataNW D := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, w, r⟩ := hd
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun u => ?_, r⟩
  have hG : (0 : ℝ) < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ (D.mem u).A.Dstar_pos
  have h0 : (0 : ℝ) < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 :=
    div_pos (mul_pos (zpow_pos hG _) hD) (by linarith)
  have := lt_of_lt_of_le h0 (w u).1
  exact_mod_cast this

theorem hd_of_window {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (tf : TFrameAt D) : HD D large₂.sc.L C' Cl Cg cb Cu cT CT :=
  ⟨GlobalTheory.Core.Deg.hypL_of h.1, dataNW_of_window h.2.2 h.2.1, tf⟩

theorem sDiagG_of_sDiag {c : ℝ} (h : SDiag c) : SDiagG c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, a, b, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, max a b, fun C' Cl p q D L _ t hd =>
    H C' Cl (le_trans (le_max_left _ _) p) (le_trans (le_max_right _ _) q) D L t hd⟩

theorem sDiagAtLed_of_sDiagG {c : ℝ} (h : SDiagG c) : SDiagAtLed c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C' Cl p q D L _ g t hd => H C' Cl p q D L g t hd⟩

theorem sDiagOn_of_sDiagAtLed {c : ℝ} (h : SDiagAtLed c) (S : Set ℝ) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 _ C' Cl p q D large₂ g t h0 tf =>
    H C' Cl p q D large₂.sc.L ⟨large₂, rfl⟩ (gammaRange_of_sizeHypotheses g h0.1) t (hd_of_window h0 tf)⟩

theorem sDiagOn_of_sDiag {c : ℝ} (h : SDiag c) (S : Set ℝ) : SDiagOn S c :=
  sDiagOn_of_sDiagAtLed (sDiagAtLed_of_sDiagG (sDiagG_of_sDiag h)) S

theorem SDiagOn.mono {S S' : Set ℝ} {c : ℝ} (hS : S ⊆ S') (h : SDiagOn S' c) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem OneOn.mono {S S' : Set ℝ} {gen : Bool} (hS : S ⊆ S') (h : OneOn S' gen) : OneOn S gen := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem OneAllOn.mono {S S' : Set ℝ} (hS : S ⊆ S') (h : OneAllOn S') : OneAllOn S := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem oneAllOn_of_oneAll (h : OneAll) (S : Set ℝ) : OneAllOn S := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 _ C' Cl p q D large₂ X Y u t h0 ct ac =>
    H C' Cl p q D large₂.sc.L X Y u t (hd_of_window h0 ct.2.2.2.2.2.2.2) ct ac⟩

theorem oneOn_of_oneLed {gen : Bool} (h : OneLed gen) (S : Set ℝ) : OneOn S gen := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, a, b, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, max a b, fun C0 _ C' Cl p q D large₂ X Y u t h0 ct ac =>
    H C' Cl (le_trans (le_max_left _ _) p) (le_trans (le_max_right _ _) q) D large₂ X Y u t h0.1
      (dataNW_of_window h0.2.2 h0.2.1) ct ac⟩

example (D : D7) (L : ℝ) (h : GamRange D L) : 8 * ((D.R.m : ℝ) ^ 5 * D.R.f * L) ≤ D.R.k := by
  have := h.1; have := h.2; linarith

example (D : D7) : ∃ L₀ : ℝ, ∀ L, L₀ < L → ¬ GamRange D L := by
  refine ⟨Real.log (AdmissibleBoundsFromSource.Gam D) / ((D.R.m : ℝ) ^ 5 * D.R.f), fun L hL h => ?_⟩
  rw [div_lt_iff₀ (pow_five_mul_f_pos D)] at hL
  have := h.1
  linarith

example (D : D7) (h : 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k) : ∃ L : ℝ, 0 < L ∧ GamRange D L := by
  refine ⟨Real.log (AdmissibleBoundsFromSource.Gam D) / ((D.R.m : ℝ) ^ 5 * D.R.f), div_pos (Real.log_pos (D.mem D.u₀).A.one_lt_gammaP) (pow_five_mul_f_pos D), ?_, h⟩
  rw [mul_div_cancel₀ _ (pow_five_mul_f_pos D).ne']

example (S : Set ℝ) (c : ℝ) (h : SDiagOn (S ∩ Set.Ici 1) c) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 h0 C' Cl p q D large₂ g t hh => H C0 ⟨h0, hh.2.2⟩ C' Cl p q D large₂ g t hh⟩
end GlobalTheory.Core.Diag
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι)

def ClsK.IsFam (j : ℕ) (hj : j ≤ D.R.m) (Φ : t.Ch j → c.Fr j → GA D (c.X j) → ℂ) : Prop :=
  ∃ val : ∀ β, A.cl j β → FrN D (ρ.N j) → ℂ, (∀ β a, val β a ∈ ValC _ (ρ.lam j)) ∧
    ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ x ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
      IsTr (ρ.r j hj x) (ρ.fr j y) y' → Φ β y (γ * (A.h j β a * x) * κ.1) = (A.chi j β κ : ℂ) * val β a y'

structure ClsK.LevT : Prop where
  stab : ∀ j, j ≤ D.R.m → ∀ β i g, g • o.Q j i = o.Q j i → ∃ h : (o.β j i).gl g ∈ A.U j β, A.chi j β ⟨_, h⟩ = 1
  dec : ∀ j, j ≤ D.R.m → ∀ β, ∀ κ ∈ A.U j β, ∃ g : ι → GL (Fin (c.X j).rank) k, (∀ i, g i • o.Q j i = o.Q j i) ∧
    ∃ κ' ∈ grpOff (c.X j) (fun x => ∃ i, x = (o.p i).v), κ = (o.I.map fun i => (o.β j i).gl (g i)).prod * κ'

structure ClsK.FullT : Prop where
  ram : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y ∈ o.Ram j
  full : ∀ j hj Φ, A.IsFam j hj Φ → (∀ β y, Φ β y ∈ o.Ram j) → ∃ ψ ∈ t.Ram j, ∀ β y, t.rd j β ψ y = Φ β y

def SOnCols (D : D7) : Prop :=
  ∀ (c : Comm D) (ρ : RealD c) (t : Tup c) (A : ClsK ρ t) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → ρ.Is → A.Forms →
    o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → A.LevT o → A.FullT o →
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → t.Col j → t.Col j, ∀ j, j ≤ D.R.m → ∀ η, ∀ ψ ∈ t.Ram j,
      S j η ψ ∈ t.Ram j ∧ ∀ β y, t.rd j β (S j η ψ) y = o.S (fun _ => η) j (t.rd j β ψ y)

def RamIff (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S : HSp D) (β : Frame p S n) (P : Pair k n)
    (g : 𝓀[k]ˣ → GL n k), (∀ s, g s • P = s • P) → ∀ φ : GA D S → ℂ,
      RamAt β P φ ↔ IsContAut S φ ∧ (∀ x, x • P = P → rTrans (β.gl x) φ = φ) ∧ ∑ᶠ s, rTrans (β.gl (g s)) φ = 0

end GlobalTheory.SeeSaw

end
end

