import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

namespace GlobalTheory.FinPl

theorem sec_mul_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) (a : AE D) (u : k) : p.sec (p.pr a * u) = a * p.sec u := by
  have h1 : p.sec (p.pr a * u) = p.sec (p.pr (a * p.sec u)) := by rw [map_mul p.pr, p.pr_sec]
  have h2 : p.e * p.sec u = p.sec u := by rw [← p.sec_pr, p.pr_sec]
  rw [h1, p.sec_pr, mul_left_comm, h2]

theorem mulVec_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) {r : ℕ} (m : Matrix (Fin r) (Fin r) (AE D)) (u : Fin r → k) :
    m *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((m.map p.pr *ᵥ u) i) := by
  funext i
  simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, sec_mul_sec]

theorem single_mem_gluedS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) :
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec := by
  refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨q.1, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
  · have h0 : (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
      funext j
      simp
    rw [h0, zero_sub]
    exact neg_mem (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Pi.single_eq_same, Unif.inv, inv_mul_cancel₀ q.ne_zero]

theorem zero_col_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), GluedCore B L₀ q β β₀ P → ∀ γ : GA D B.V₀, (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i)) ∈ latV B.V₀ L₀ (· = p.v) := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hg γ hpres
  have he : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have hvec : p.sec 1 • ratV (vecB B.o B.ζ) =
      fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, he, mulVec_single_one, hg.sum]
    simp [p.sec_pr]
  have hmem : p.sec 1 • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by
    rw [hg.unit.2, hvec, ← hg.lat]
    exact single_mem_gluedS q P
  have := hpres _ hmem
  rwa [hg.unit.2, hvec] at this

theorem orbitGlued (D : D7) : OrbitGlued D := by
  intro k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ hγ hpres
  obtain ⟨hF1, -, -, hF4, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨h, rfl⟩ := (hF1 γ).1 hγ
  have key : ∀ x, mt B.V₀ (β₀.gl h)⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) ↔
      x ∈ h • gluedS q 1 P.ker P.vec := by
    intro x
    rw [← map_inv, mulVec_sec, β₀.gl_mat, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, β₀.b'b,
      Matrix.mul_one, ← mulVec_mulVec, ← hg.lat, GlobalTheory.LatPair.mem_smul_iff]
    rfl
  have hz := (key _).1 (zero_col_mem D k p n q σ B L₀ β β₀ P hg _ hpres)
  have hint : ∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] :=
    fun x hx => GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral D k p n q σ B L₀ β β₀ P hsd hg _ hγ hpres x ((key x).2 hx)
  rcases GlobalTheory.T.smul_gluedLatticeFirstPosition_cases k n q P h hz hint with ⟨Λ, hΛ, hM | hM⟩ | ⟨g, hM⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inl fun x => by rw [← hM]; exact (key x).symm⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inr fun x => by rw [← hM]; exact (key x).symm⟩
  · obtain ⟨hA1, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hF4 L₀ hsd
    have hΛG : Λ₀ = gluedS q 1 P.ker P.vec := Submodule.ext fun x => (hΛ₀ x).trans (hg.lat x).symm
    refine Or.inl ⟨β.gl g, (hA1 _).2 ⟨g, rfl⟩, β₀.gl ((embX 1 g)⁻¹ * h), ?_, ?_⟩
    · rw [hK, hΛG, mul_smul, hM, inv_smul_smul]
    · rw [GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal D k p n σ B β β₀ hg.sum g, ← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mem_latV_iff (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) (w : Fin S.rank → k) :
    (fun i => q.sec (w i)) ∈ latV S L (· = q.v) ↔ ∀ i, w i ∈ 𝒪[k] := by
  classical
  have hmem : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hsingle : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ L := fun i =>
    (hmem _).2 fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
  let G : Finset (Fin S.rank → D.host.E) := Finset.univ.image fun i => Pi.single i 1
  have hGL : ∀ x ∈ (G : Set (Fin S.rank → D.host.E)), x ∈ L := by
    intro x hx
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hsingle i
  have hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact hGL
    · intro x hx
      have hi := (hmem x).1 hx
      have e : x = ∑ i, (⟨x i, hi i⟩ : 𝓞 D.host.E) • (Pi.single i 1 : Fin S.rank → D.host.E) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
        simp [Algebra.smul_def]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G]))
  constructor
  · intro h
    have h1 := FullLatFrame.pr_mem_span q G hG h
    simp only [q.pr_sec] at h1
    have h2 : ∀ z ∈ Submodule.span 𝒪[k] (FullLatFrame.aux₃ q '' (G : Set (Fin S.rank → D.host.E))), ∀ i, z i ∈ 𝒪[k] := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        intro i
        exact FullLatFrame.pr_int_mem q ⟨x i, (hmem x).1 (hGL x hx) i⟩
      | zero => intro i; exact zero_mem _
      | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
      | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
    exact h2 _ h1
  · intro h
    have e : w = ∑ i, (⟨w i, h i⟩ : 𝒪[k]) • FullLatFrame.aux₃ q (S := S) (Pi.single i 1) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [FullLatFrame.aux₃, Pi.single_apply, Ne.symm hb]) (by simp)]
      simp [FullLatFrame.aux₃]
      change _ = w j * 1
      rw [mul_one]
    rw [← FullLatFrame.mem_latW, e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [FullLatFrame.mem_latW]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (hsingle i)

theorem intIn_stdFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : IntIn q S (stdFr k e) L := by
  intro y
  rw [sec_mem_latV_iff q S L hL]
  have h : (stdFr k e).β *ᵥ y = y ∘ e.symm := by
    change (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e *ᵥ y = _
    have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin S.rank) (Fin S.rank) k) y id e
    simpa [Function.comp_def] using this
  rw [h]
  exact ⟨fun h i => h _, fun h a => by simpa using h (e a)⟩

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFr {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (e : Y ≃ Fin N) (d : Y → k) (hd : ∀ y, d y ≠ 0) :
    GlobalTheory.LocMod.Frame k N Y where
  β := (stdFr k e).β * Matrix.diagonal d
  γ := Matrix.diagonal (fun y => (d y)⁻¹) * (stdFr k e).γ
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      show (fun y => d y * (d y)⁻¹) = fun _ => (1 : k) from funext fun y => mul_inv_cancel₀ (hd y),
      Matrix.diagonal_one, Matrix.one_mul, (stdFr k e).βγ]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (stdFr k e).γ, (stdFr k e).γβ, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      show (fun y => (d y)⁻¹ * d y) = fun _ => (1 : k) from funext fun y => inv_mul_cancel₀ (hd y), Matrix.diagonal_one]

theorem intIn_diagFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) (d : Y → k) (hd : ∀ y, d y ≠ 0) (hv : ∀ y, valuation k (d y) = 1) :
    IntIn q S (diagFr e d hd) L := by
  intro y
  have h1 := intIn_stdFr q S L hL e (fun a => d a * y a)
  have h2 : (diagFr e d hd).β *ᵥ y = (stdFr k e).β *ᵥ fun a => d a * y a := by
    change ((stdFr k e).β * Matrix.diagonal d) *ᵥ y = _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact Matrix.mulVec_diagonal _ _ _
  rw [h2, ← h1]
  refine forall_congr' fun a => ?_
  change valuation k (y a) ≤ 1 ↔ valuation k (d a * y a) ≤ 1
  rw [map_mul, hv, one_mul]

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

theorem oTop_iA {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

theorem oTop_iB {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iB b a = if (I.rec7 l Z).sp.X'.rank = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

theorem entry_inl {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ} {Y : Type} [Fintype Y]
    [DecidableEq Y] (eT : Y ≃ Fin n) (iA : Matrix (Fin N) (Fin n) E) (hA : ∀ b a, iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0)
    (r : Fin N) (c : Y) (m : Fin N) (hm : (m : ℕ) = eT c) :
    (1 : Matrix (Fin N) (Fin N) k) r m = (iA.map f * (1 : Matrix (Fin n) (Fin n) k).submatrix id eT) r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (eT c)
    (fun b _ hb => by rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]) (by simp)]
  rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, hA, Matrix.one_apply]
  by_cases h : (eT c : ℕ) = r
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

theorem entry_inr {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ}
    (iB : Matrix (Fin N) (Fin 1) E) (hB : ∀ b a, iB b a = if n = (b : ℕ) then 1 else 0) (z : Fin 1 → E) (x : E)
    (hz : ∀ i, z i = x) (r : Fin N) (m : Fin N) (hm : (m : ℕ) = n) :
    (1 : Matrix (Fin N) (Fin N) k) r m * f x = (iB.map f *ᵥ fun i => f (z i)) r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, hB, hz, Matrix.one_apply]
  by_cases h : n = (r : ℕ)
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

set_option maxHeartbeats 4000000 in

theorem exists_locX_std : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : AllTrue W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (pk W).ΛX) (pk W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((pk W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (pk W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _

  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (pk W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]

end GlobalTheory.XGeoStd.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.VacTheta

theorem isFinComb_of_combAt {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ}
    (h : GlobalTheory.FinPl.CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this

theorem main : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (pk W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (pk W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (pk W).ψ _ _ (comb (pk W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha hTr j hj
  have hv := hTr.pinX.vc j (by omega)
  refine ⟨hv.2.theta, hv.2.lat, ?_⟩
  exact (GlobalTheory.HeisComb.main _ (pk W).ψ _ _).2.2.1 (a.v.dT j) (a.g.vac j) hv.2.theta
    (isFinComb_of_combAt (ha.vis.atT j).1) hv.1

end GlobalTheory.Fam.VacTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.TopFrame

theorem sumE_one_single {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) (t : Eˣ) (r b : Fin N) :
    GlobalTheory.TopStep.sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = N then (t : E) else 1) else 0 := by
  rcases GlobalTheory.TopStep.idx_cases hN r with ⟨i, rfl⟩ | rfl
  · have h := congrFun (GlobalTheory.TopStep.prH_sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1)) i
    refine h.trans ?_
    show (Pi.single b (1 : E) : Fin N → E) (Formalism.L2.Col.Br.iC hN i) = _
    have hi : ¬ (Formalism.L2.Col.Br.iC hN i).val + 1 = N := by
      show ¬ i.val + 1 = N
      have := i.2
      omega
    rw [if_neg hi, Pi.single_apply]
    simp only [Fin.ext_iff]
  · have hi : (Formalism.L2.Col.Br.iL hN).val + 1 = N := by
      show n + 1 = N
      omega
    rw [GlobalTheory.TopStep.sumE_last, if_pos hi, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> simp

theorem frsF_top {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (hI : I.Ok) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (j : ℕ) (hj : j = B.R.m) (β : Ch₀ j) (r b : Fin (B.R.N j)) :
    Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := by
  subst hj
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hPr := (base_fields_primes_ok B X).2.1
  have hπ := GlobalTheory.Mem.Col2.PerLaw.piT_notMem_Q hI u a
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have h2 := h1.fr ⟨P.1, hQ⟩ r b
  have h3 := (hA.base _ le_rfl β).1.fr ⟨P.1, hSQ⟩ r b
  have h4 := (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective (h3.symm.trans h2)
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩, h4, tilF_fr I.sel (I.tup a) hPr u hπ]
  refine (sumE_one_single _ _ r b).trans ?_
  rw [unitOf_val (hπ ⟨P.1, hQ⟩)]

set_option maxHeartbeats 1600000 in

theorem baseFr_top_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : QJ a t), J.Reads → ∀ i (hm : (J.G i).s + 1 + 1 ≤ B.R.m) (γ : J.Ch₀ ((J.G i).s + 1 + 1)) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((J.G i).s + 1)) (Fin B.R.t) ((J.G i).s + 2) ⊕ Unit ≃ Fin (B.R.N ((J.G i).s + 1 + 1))), GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e → ∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b)) = (J.G i).FM.β r b := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hiA t J hJ i hm γ e he r b
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have key : ∀ j (h : j = (I.rec7 l Z).R.m), (∀ r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0) ∧
      ∀ r, vecB (a.g.oT j h) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro j h
    subst h
    exact ⟨hiA, fun r => hat.z0 r⟩
  obtain ⟨hA, hz⟩ := key _ (J.G i).hs
  obtain ⟨-, ⟨e', he', hT'⟩, hz0⟩ := ha.stdQ (J.pl i) ⟨t, J.mem i⟩
  let ι : (I.rec7 l Z).host.E →+* (J.G i).k := (J.G i).q.pr.comp (incA (I.rec7 l Z))
  have hL := frsF_top J.A hJ.is hW.tr.ok (J.P i) (hJ.tw i).nmem _ hs γ (finCongr (rankN (I.rec7 l Z) _ hm) r) (e b)
  have hL' : baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b) =
      if r.val = (e b).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := hL
  have hN : B.R.N ((J.G i).s + 1 + 1) = B.R.N B.R.m := congrArg _ hs
  refine (congrArg _ hL').trans (Eq.trans ?_ (congrFun (congrFun (J.G i).last r) b).symm)
  rcases b with b | b
  · have hb : (e (Sum.inl b)).val = (e' b).val := (he _).trans (he' b).symm
    have hb2 : (e (Sum.inl b)).val + 1 ≠ B.R.N B.R.m := by
      intro h
      have h2 : (e (Sum.inr ())).val = B.R.N B.R.m - 1 := he _
      have h3 : e (Sum.inl b) = e (Sum.inr ()) := Fin.ext (by omega)
      exact Sum.inl_ne_inr (e.injective h3)
    have h5 : (if r.val = (e (Sum.inl b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        (a.g.oT _ (J.G i).hs).iA r (e' b) := by
      refine Eq.trans ?_ (hA r (e' b)).symm
      rw [← hb]
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb2
      · rfl
      · rfl
    refine (congrArg _ h5).trans ?_
    show _ = ∑ c, ι ((a.g.oT _ (J.G i).hs).iA r c) * (J.G i).FT.β c b
    have h6 : ∀ c, (J.G i).FT.β c b = if c = e' b then 1 else 0 := fun c => (congrFun (congrFun hT' c) b).trans Matrix.one_apply
    refine Eq.symm ((Finset.sum_congr rfl fun c _ => congrArg _ (h6 c)).trans ?_)
    refine (Finset.sum_eq_single (e' b) (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · exact (congrArg _ (if_neg hc)).trans (mul_zero _)
    · exact (congrArg _ (if_pos rfl)).trans (mul_one _)
  · have h2 : (e (Sum.inr b)).val = B.R.N B.R.m - 1 := he _
    have h3 := (e (Sum.inr b)).2
    have h4 : (if r.val = (e (Sum.inr b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        vecB (a.g.oT _ (J.G i).hs) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r := by
      rw [hz]
      split_ifs with h5 h6 h7
      · rfl
      · omega
      · omega
      · rfl
    refine (congrArg _ h4).trans ?_
    show ι (∑ c, (a.g.oT _ (J.G i).hs).iB r c * (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) c) = ∑ c, ι ((a.g.oT _ (J.G i).hs).iB r c) * (J.G i).z₀ c
    exact (map_sum ι _ _).trans (Finset.sum_congr rfl fun c _ => (map_mul ι _ _).trans (congrArg _ (congrFun hz0 c).symm))

end GlobalTheory.Fam.TopFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_step_constants_tuple_indep : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → RealZetaQ D → Restore D → ∀ h : RangeX R, RChain R h → RMeas R → RVol R → RNrm R → RUnif R h := by
  first | exact @GlobalTheory.ChainTw.UnifFree.rUnif_of | exact GlobalTheory.ChainTw.UnifFree.rUnif_of | (intros; apply GlobalTheory.ChainTw.UnifFree.rUnif_of <;> assumption)
end

