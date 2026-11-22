import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem cA_xi : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [FrameLat.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]

theorem cA_xi_inv : cA D (incA D D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := by
  rw [FrameLat.cA_incA, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, RingHom.map_neg]

theorem last_of {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ}
    (hb : ∀ r : Fin ρ, r.1 + 1 = ρ → b r = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV W LW (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hρ : 0 < ρ) : ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hr : (⟨ρ - 1, by omega⟩ : Fin ρ).1 + 1 = ρ := by simp only; omega
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _ _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb _ hr, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem herm_kap {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'') (l : Fin L.rank → AE D)
    (s : Fin S.rank → AE D) :
    hermAt S ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ l) s =
      incA D (-D.host.xi0⁻¹) * hermAt L l ((rat τ : Mx D _ _) *ᵥ ((show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s)) := by
  rw [mulVec_mulVec]
  change hermAt S ((incA D (-D.host.xi0⁻¹) • (giA S ⬝ (adj (rat τ ⬝ w) ⬝ gA L))) *ᵥ l) s = _
  generalize ((rat τ : Mx D _ _) ⬝ w : Mx D L.rank S.rank) = u
  rw [herm_eq, herm_eq, mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, dotProduct_mulVec]
  congr 2
  funext i
  simp only [vecMul, mulVec, dotProduct, adj, map_sum, RingHom.map_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem kap_of {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α μ : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hm : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * μ * inU lam hlam * (xiU D * cU α)⁻¹)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x) := by
  intro w hw
  rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ] at hw
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hmx : MxAt (· = x) (kap τ S w) := mxAt_smul _ (mxAt_mul _ (mxAt_mul' _ (mxAt_adj (mxAt_mul _ hw.1))))
  rw [LatMem.mem_latO_iff D L S LL LS hLL hLS]
  refine ⟨hmx, fun l hl => ?_⟩
  have hn := line_norm hζ hLL hm
  obtain ⟨a, ha, rfl⟩ := line_vec hζ (latV_idAt hl)
  rw [hα]
  refine (hsd.2.2 _ ?_).2 ?_
  · exact fun i => Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (latV_idAt hl) i)
  intro s hs
  have h1 := (hα _ _ _).1 (hw.2 s hs)
  obtain ⟨a', ha', e'⟩ := line_vec hζ₀ (latV_idAt h1)
  rw [e'] at h1
  have e2 : (show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s = ((α : AE D) * a') • ratV ζ₀ := by
    rw [mul_smul, ← e', smul_smul, Units.mul_inv, one_smul]
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, e2, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat]
  have h2 := int_mul ((hm a ha).1 hl) (int_conj.2 ((hμ a' ha').1 h1))
  rw [hn _ h2.1] at h2
  convert h2 using 1
  generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m
  have f1 := m.mul_inv
  have f2 : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
  have f3 : cA D (m : AE D) = cA D α * cA D μ * cA D (incA D lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, RingHom.map_mul, inU_val, cU_inv, cA_cA, xiU, inU_inv, cA_xi_inv]
  rw [f3]
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one]
  generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = h
  linear_combination (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a') * f2 +
    (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a' * (cA D μ * cA D (μ⁻¹ : (AE D)ˣ))) * f1

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem isU_xi (h : p.UnitAA) : IsU p.v (xiU D : AE D) :=
  IsU.of_pres (xiU D).mul_inv (fun a ha => (h.1 a ha).1) fun a ha => (h.1 a ha).2

theorem isU_alpha (h : p.UnitAA) {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = p.v) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = p.v)) :
    IsU p.v (α : AE D) := by
  obtain ⟨e, he, hg⟩ := line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 p.v
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h.2, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

theorem val_le_one {u : AE D} (h : IsU p.v u) : valuation k (p.pr u) ≤ 1 := by
  refine (p.int_iff _).2 ?_
  rw [p.sec_pr, mul_comm]
  exact ((h _ (FrameLat.e_mem_idAt p)).1 (FrameLat.e_mem_intAt p)).2

theorem val_eq_one {u : (AE D)ˣ} (h : IsU p.v (u : AE D)) : valuation k (p.pr u) = 1 := by
  have h1 := val_le_one h
  have h2 := val_le_one (h.inv u.mul_inv)
  have h3 : valuation k (p.pr u) * valuation k (p.pr (u⁻¹ : (AE D)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by rw [← h3]; exact mul_le_of_le_one_right' h2)

end Split

end GlobalTheory.GoodPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFrameMatrixIffMemSplitHalfHomLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def frameAt {N : ℕ} (π' : EAf D →+* k) (β : GL (Fin N) (EAf D)) : GlobalTheory.LocMod.Frame k N (Fin N) where
  β := β.val.map π'
  γ := (β⁻¹).val.map π'
  βγ := by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  γβ := by rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D} (q : GlobalTheory.FinPl.SplitPt D k) {π' : EAf D →+* k}
  (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem down_eq (hπ : ∀ a, π' (toEAf D a) = q.pr a) (x : WO S T) :
    (ofSplit q).down (frameAt π' βS) (frameAt π' βT) x = (frMapO S T βS βT x).map π' := by
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map q.pr := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h2]
  rfl

theorem up_down {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_up {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ :=
    Matrix.ext fun i j => p.π_ι _
  rw [this]
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem frMapO_smul (a : AE D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) :
    frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem smul_mem_at {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : WO S T}
    (hx : x ∈ latO S T LS LT fun _ => True) : q.e • x ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, hε, h⟩ := q.above
  have h1 : IsPlaceIdem D q.v (pairA _ 0 (GlobalTheory.VacUnion.idemF q.v)) :=
    ⟨_, rfl, by rw [GlobalTheory.VacUnion.evalV_idemF, if_pos rfl], fun w hw => by rw [GlobalTheory.VacUnion.evalV_idemF, if_neg hw]⟩
  have h2 : GlobalTheory.VacUnion.idemE q.v = q.e + cA D q.e := by
    rw [h, GlobalTheory.IdemSupport.placeIdem_unique hε h1]; rfl
  have h3 := GlobalTheory.VacUnion.idemE_smul_mem q.v (GlobalTheory.PlaceModelSum.idem_smul_latO q.split.1 hx)
  have h4 : GlobalTheory.VacUnion.idemE q.v * q.e = q.e := by
    rw [h2]
    linear_combination q.split.1 + q.split.2.1
  rwa [smul_smul, h4] at h3

theorem latO_le_top {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, k⟩ => ⟨α, hα, fun _ hw => (hw trivial).elim, k⟩

theorem eq_sum {r : ℕ} {a : Fin r → AE D} {pl : Fin r → Formalism.L2.DIV.Pl D.host.E} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i)) (hinj : Function.Injective pl) (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    (he : IsIdemSum e Q) : e = ∑ i, a i := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  refine (Finset.sum_bij (fun i _ => pl i) (fun i _ => (hQ _).2 ⟨i, rfl⟩) (fun i _ j _ h => hinj h)
    (fun PP hPP => by obtain ⟨i, hi⟩ := (hQ PP).1 hPP; exact ⟨i, Finset.mem_univ _, hi⟩) fun i _ => ?_).symm
  exact GlobalTheory.IdemSupport.delta_unique hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (ha i))
    (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (h1 _ ((hQ _).2 ⟨i, rfl⟩)))

theorem isIntM_iff_mem_latO : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D r k _ _ _ _ q pl Q e hq hu hinj hQ he S T LS LT hS hT βS βT hβ x hx
  choose π' hπ hrest using fun i => GlobalTheory.FinPl.SplitPt.exists_lift_isRed D (k i) (q i) (pl i) (hq i)
  have hint := fun i => (hrest i).2.1
  have he' : e = ∑ i, (q i).e := eq_sum hq hinj hQ he
  have hxe : e • x = x := Matrix.ext fun i j => hx i j
  constructor
  · intro h
    rw [← hxe, he', Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have h1 := GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
      (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 ((frMapO S T βS βT x).map (π' i)) fun a b => ((hint i _).1 (h a b)).2
    rw [← down_eq (q i) βS βT (hπ i), up_down] at h1
    exact latO_le_top h1
  · intro h a b
    rw [← hxe, frMapO_smul, he', GlobalTheory.FunObj.Comparison₂.hom_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => (hint i _).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, sub_mul, one_mul, ← RingHom.map_mul, (q i).split.1, sub_self, zero_mul]
      exact zero_mem _
    · obtain ⟨y, hy, h1⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
        (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 _ (smul_mem_at (q i) h)
        (fun a b => by
          change (q i).e * ((q i).e * _) = (q i).e * _
          rw [← mul_assoc, (q i).split.1])
      have h2 := down_eq (q i) βS βT (hπ i) ((q i).e • x)
      rw [h1, down_up, ← h1] at h2
      rw [← frMapO_smul]
      have h3 := hy a b
      rw [h2] at h3
      exact h3

end GlobalTheory.HalfInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpace
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnFockRev

theorem killed_of_subfamily {P Q V : Type} [AddCommGroup V] [Module ℂ V] (b : Q → V → V) (ι : P → Q) (T : V → Prop)
    (hb : ∀ q f, T f → T (b q f)) (hT : ∀ (c : ℂ) f, T f → T (c • f))
    (hadd : ∀ q f g, T f → T g → b q (f + g) = b q f + b q g)
    (hsmul : ∀ q (c : ℂ) f, b q (c • f) = c • b q f)
    (hdec : ∀ q, ∃ (p p' : P) (c : ℂ), ∀ f, T f → b q f = b (ι p) f + c • b (ι p') f) (N : ℕ) :
    ∀ f, T f → (∀ l : List P, l.length = N → (l.map ι).foldr b f = 0) →
      ∀ l : List Q, l.length = N → l.foldr b f = 0 := by
  have wT : ∀ (l : List Q) f, T f → T (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, T f → T g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have wsmul : ∀ (l : List Q) (c : ℂ) f, l.foldr b (c • f) = c • l.foldr b f := fun l c f => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hsmul]; rfl
  have step : ∀ (M : ℕ) (f : V) (p : P), (∀ l : List P, l.length = M + 1 → (l.map ι).foldr b f = 0) →
      ∀ l : List P, l.length = M → (l.map ι).foldr b (b (ι p) f) = 0 := fun M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.map_append, List.foldr_append] at this
  induction N with
  | zero =>
    intro f _ k l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact k [] rfl
  | succ N ih =>
    intro f hf k l hl
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    obtain ⟨p, p', c, h⟩ := hdec q
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, h f hf,
      wadd _ _ _ (hb _ _ hf) (hT _ _ (hb _ _ hf)), wsmul,
      ih _ (hb _ _ hf) (step _ _ _ k) l' hl', ih _ (hb _ _ hf) (step _ _ _ k) l' hl', smul_zero, add_zero]

theorem dRho_smul_fun {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, Pi.smul_apply, smul_eq_mul]
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_of_sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB → IsFockVec ψ θ (dblSp A) B s' sB f := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hth hf
  obtain ⟨N, hN⟩ := GlobalTheory.T.fockPolynomialSchwartz_killed_by_longAnnihilation D θ hθ B A.rank l sB hsB _ hf
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  refine ⟨hth, N, ?_⟩
  refine killed_of_subfamily (P := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (fun p g => annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g)
    (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))) (IsThetaFunO ψ (dblSp A) B)
    (fun q g hg => isThetaFunO_annih_of_std hψ hθ hν _ _ _ hg)
    (fun c g hg => (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν g g hg hg c).2.1)
    (fun q g g' hg hg' => ?_) (fun q c g => ?_) (fun q => ?_) N f hth (fun L hL => ?_)
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', smul_add]
    abel
  · simp only [annih]
    rw [dRho_smul_fun, dRho_smul_fun, smul_add, smul_comm]
  · obtain ⟨X, X', c, h⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ hψ θ hθ A B μ hμ s' sB hs' hsB q.1 q.2
    exact ⟨(q.1, X), (q.1, X'), c, h⟩
  · exact GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ hψ A B ν 𝓨 hν _ (key L).1 ((key L).2.trans (hN L hL))

end GlobalTheory.StdUnnFockRev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms GlobalTheory.StepData
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LocMod.IntFrameStd

variable {D : D7}

theorem isSelfDualC_of_gram_one {S : HSp D} (hG : S.gram = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) : IsSelfDualC S L := by
  have hm : ∀ x : Fin S.rank → D.host.E, x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocMod.IntFrameStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports
section
noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
end
end

