import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

variable (G i j) in

abbrev PtS : Type := Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)

variable (G i j) in

abbrev IxS : Type := Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)

variable (G) in

abbrev HomA (t : T) (i j : ℕ) : Type := WO (G.pS (.mu t i j)) (G.pT (.mu t i j))

variable (G i j) in

abbrev HomB : Type := WO (G.pS (.chi i j)) (G.pT (.chi i j))

abbrev mapA (t : T) (e : Num G i j) (u : PtS G i j) : HomA G t i j := mulG (spW₁ G i j) (colV e u)ᵀ

abbrev mapB (e : Num G i j) (u : PtS G i j) : HomB G i j := adjV₁ e u

def ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : PtS G i j :=
  (fromCols (GlobalTheory.BigDat.divG (spW₁ G i j) x.1)ᵀ ((GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapA_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapA t e (ofMaps t e x) = x.1 := by
  have h1 : (colV e (ofMaps t e x))ᵀ = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (spW₁ G i j)) h1).trans (GlobalTheory.BigDat.mulG_divG _ _)

theorem mapB_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapB e (ofMaps t e x) = x.2 := by
  have h2 : ((ofMaps t e x).submatrix id fun k => e (.inr k)).map (cA D) = GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) :=
    Matrix.ext fun a b => by
      simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
        GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (t : T) (e : Num G i j) (u : PtS G i j) : ofMaps t e (mapA t e u, mapB e u) = u := by
  have h1 : GlobalTheory.BigDat.divG (spW₁ G i j) (mapA t e u) = (colV e u)ᵀ := GlobalTheory.BigDat.divG_mulG _ _
  have h2 : GlobalTheory.BigDat.divG (spV₁ G i j) (-mapB e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (GlobalTheory.BigDat.divG (spV₁ G i j)) (neg_neg _)).trans (GlobalTheory.BigDat.divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapA_add (t : T) (e : Num G i j) (u u' : PtS G i j) : mapA t e (u + u') = mapA t e u + mapA t e u' :=
  GlobalTheory.RouteCoords.mulG_colV_add e u u'

theorem mapB_add (e : Num G i j) (u u' : PtS G i j) : mapB e (u + u') = mapB e u + mapB e u' :=
  GlobalTheory.RouteCoords.adjV₁_add e u u'

theorem mapA_smul (t : T) (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapA t e (c • u) = c • mapA t e u :=
  GlobalTheory.BigDat.mulG_smul (spW₁ G i j) c (colV e u)ᵀ

theorem mapB_smul (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapB e (c • u) = c • mapB e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans
    ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (t : T) (e : Num G i j) : PtS G i j ≃ₗ[AF D.host.F] HomA G t i j × HomB G i j where
  toFun u := (mapA t e u, mapB e u)
  invFun := ofMaps t e
  map_add' u u' := Prod.ext (mapA_add t e u u') (mapB_add e u u')
  map_smul' c u := Prod.ext (mapA_smul t e c u) (mapB_smul e c u)
  left_inv := ofMaps_maps t e
  right_inv x := Prod.ext (mapA_ofMaps t e x) (mapB_ofMaps t e x)

theorem maps_apply (t : T) (e : Num G i j) (u : PtS G i j) : maps t e u = (mapA t e u, mapB e u) := rfl

abbrev sympS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : PtS G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

theorem sympS_eq (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : PtS G i j) :
    sympS Γ x x' = symplO _ _ (mapA t e x) (mapA t e x') + symplO _ _ (mapB e x) (mapB e x') :=
  GlobalTheory.RouteCoords.symp_eq t e Γ hW₁ hWW x x'

def boxS (t : T) (e : Num G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (u : PtS G i j) : ℂ :=
  f₁ (mapA t e u) * f₂ (mapB e u)

def heisS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f : PtS G i j → ℂ)
    (u : PtS G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympS Γ u u₀) * f (u + u₀)

theorem heisS_box (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) :
    heisS Γ ψ u₀ (boxS t e f₁ f₂) = boxS t e (heisO ψ _ _ (mapA t e u₀) f₁) (heisO ψ _ _ (mapB e u₀) f₂) := by
  funext u
  unfold heisS boxS heisO symplOH
  rw [sympS_eq t e Γ hW₁ hWW, mul_add, AddChar.map_add_eq_mul, mapA_add, mapB_add, GlobalTheory.BigDat.invOf_two]
  ring

abbrev thetaS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u : PtS G i j) : ℂ := thetaSum D.host.F (Γ.M'.co.rho ψ u Φ)

theorem thetaS_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u₀ : PtS G i j) : thetaS Γ ψ (Γ.M'.co.rho ψ u₀ Φ) = heisS Γ ψ u₀ (thetaS Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Γ.M'.co ψ u u₀ Φ)).trans tsum_mul_left

theorem thetaS_smul (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (IxS G i j → AF D.host.F) → ℂ) (u : PtS G i j) : thetaS Γ ψ (c • Φ) u = c * thetaS Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left

variable (G) in

abbrev latA (t : T) (i j : ℕ) : AddSubgroup (HomA G t i j) :=
  latO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) fun _ => True

variable (G i j) in

abbrev latB : AddSubgroup (HomB G i j) :=
  latO (G.pS (.chi i j)) (G.pT (.chi i j)) (G.latS (.chi i j) : Set _) (G.latT (.chi i j) : Set _) fun _ => True

def latPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (PtS G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapA t e 0 = 0 from congrArg Prod.fst (map_zero (maps t e))]; exact zero_mem _, by
    rw [show mapB e 0 = 0 from congrArg Prod.snd (map_zero (maps t e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapA_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapB_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapA t e (-a) = -mapA t e a from congrArg Prod.fst (map_neg (maps t e) a)]; exact neg_mem ha.2.1, by
    rw [show mapB e (-a) = -mapB e a from congrArg Prod.snd (map_neg (maps t e) a)]; exact neg_mem ha.2.2⟩

def genPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : Set (PtS G i j) :=
  {γ | (∃ γ' ∈ latPtS t e v, γ = 2 • γ') ∨ γ ∈ latPtS t e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ GlobalTheory.FlipMatch.mixHalfS e ε}

theorem genPtS_subset (t : T) (e : Num G i j) (v : Pl D.host.F) : genPtS t e v ⊆ latPtS t e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

end GlobalTheory.SmallDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinSupp

theorem eq_zero_of_parts {D : D7} {m n : ℕ} (z : Mx D m n) (h1 : z.map (infPart D) = 0) (h2 : z.map (finPart D) = 0) : z = 0 := by
  apply (GlobalTheory.AscFinInhab.coordH D m n).injective
  rw [GlobalTheory.AscFinInhab.coordH_apply, GlobalTheory.AscFinInhab.coordH_apply, (GlobalTheory.AscFinInhab.RCh_eq_zero_iff z).2 h1,
    (GlobalTheory.AscFinInhab.FCh_eq_zero_iff z).2 h2, map_zero, map_zero]

theorem smul_eInf_eq_zero {D : D7} {m n : ℕ} (a : Mx D m n) (h : a.map (infPart D) = 0) :
    GlobalTheory.FinTranslate.eInf D • a = 0 := by
  apply eq_zero_of_parts
  · ext i j
    have h0 : infPart D (a i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]
  · ext i j
    exact GlobalTheory.ThetaClosed.finPart_eInf_smul (a i j)

theorem smul_one_sub_eInf_eq_zero {D : D7} {m n : ℕ} (r : Mx D m n) (h : r.map (finPart D) = 0) :
    (1 - GlobalTheory.FinTranslate.eInf D) • r = 0 := by
  apply eq_zero_of_parts
  · ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (r i j)
  · ext i j
    have h0 : finPart D (r i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]

theorem upper_of_UX {D : D7} {ρ : ℕ} (u : UX D ρ) : ∀ i j, j ≤ i → ((u.1.1 : Mx D ρ ρ) - 1) i j = 0 := by
  have hU : (u.1 : GL (Fin ρ) (AE D)) ∈ GlobalTheory.UniIndexPrime.uniSub ρ (AE D) := u.2
  rw [GlobalTheory.UniIndexPrime.mem_uniSub] at hU
  obtain ⟨h1, h2⟩ := hU
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · have e1 : (u.1.1 : Mx D ρ ρ) i j = 0 := h1 i j h
    have e2 : (1 : Mx D ρ ρ) i j = 0 := Matrix.one_apply_ne (ne_of_gt h)
    rw [Matrix.sub_apply, e1, e2, sub_zero]
  · subst h
    have e1 : (u.1.1 : Mx D ρ ρ) j j = 1 := h2 j
    rw [Matrix.sub_apply, e1, Matrix.one_apply_eq, sub_self]

theorem split_parts {D : D7} {m ρ : ℕ} (x : Mx D m ρ) (N : Mx D ρ ρ) (r a : Mx D m ρ) (hxN : x ⬝ N = r + a)
    (hr : r.map (finPart D) = 0) (ha : a.map (infPart D) = 0) :
    x ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • N) = a ∧ x ⬝ (GlobalTheory.FinTranslate.eInf D • N) = r := by
  have hea := smul_eInf_eq_zero a ha
  have her := smul_one_sub_eInf_eq_zero r hr
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, hxN, smul_add, her, zero_add, sub_smul, one_smul, hea, sub_zero]
  · rw [Matrix.mul_smul, hxN, smul_add, hea, add_zero]
    have h := her
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm

theorem main_part {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (u : UX D ρ) (N : Mx D ρ ρ) (hN : (u.1.1 : Mx D ρ ρ) = 1 + N)
    (h1 : psiE ψ (upSum ((1 - GlobalTheory.FinTranslate.eInf D) • N)) = 1) :
    psiUni ψ u.1 = psiE ψ (upSum (GlobalTheory.FinTranslate.eInf D • N)) := by
  have hsplit : N = GlobalTheory.FinTranslate.eInf D • N + (1 - GlobalTheory.FinTranslate.eInf D) • N := by
    rw [sub_smul, one_smul, add_sub_cancel]
  show psiE ψ (upSum u.1.1) = _
  rw [hN, GlobalTheory.AscFinInhab.upSum_add', GlobalTheory.AscFinInhab.upSum_one', zero_add, hsplit,
    GlobalTheory.AscFinInhab.upSum_add', psiE_add, h1, mul_one, ← hsplit]

theorem charOnSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (L : Matrix (Fin ρ) (Fin W.rank) D.host.E), L * x₀ = 1 → p.Is dV dW (rat x₀) ψ → ∀ (u : UX D ρ) (r : Mx D W.rank ρ), r.map (finPart D) = 0 → rat x₀ ⬝ u.1.1 - (rat x₀ + r) ∈ p.A₁ → psiUni ψ u.1 = psiE ψ (upSum (rat L ⬝ r)) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr ha
  have haInf : (rat x₀ ⬝ u.1.1 - (rat x₀ + r)).map (infPart D) = 0 :=
    (GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hp.a₁.fin _ ha)
  have hxN : rat x₀ ⬝ ((u.1.1 : Mx D ρ ρ) - 1) = r + (rat x₀ ⬝ u.1.1 - (rat x₀ + r)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  obtain ⟨h1e, he⟩ := split_parts _ _ _ _ hxN hr haInf
  have hLr : rat L ⬝ r = GlobalTheory.FinTranslate.eInf D • ((u.1.1 : Mx D ρ ρ) - 1) := by
    rw [← he, ← Matrix.mul_assoc, ← rat_mul, hL, rat_one, Matrix.one_mul]
  have hfin : MxAt (fun _ => True) ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) := by
    rw [GlobalTheory.AscFinInhab.mxAt_true_iff]
    ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have hup' : ∀ i j, j ≤ i → ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) i j = 0 := by
    intro i j hij
    rw [Matrix.smul_apply, upper_of_UX u i j hij, smul_zero]
  have hmem : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ ⬝ (rat x₀ ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))) ∈ p.A₁ := by
    rw [inv_one, GlobalTheory.AscFinInhab.mt_one_, Matrix.one_mul, h1e]; exact ha
  have hshift := (GlobalTheory.AscFin.cond_one hp (0 : Mx D V₀.rank σ)).shift _ hfin hup' hmem
  rw [hLr]
  exact main_part ψ u _ (by rw [add_sub_cancel]) hshift

end GlobalTheory.AscFinSupp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows.Good

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem princGL_le_princAt (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} {PP : Pl E} (h : I ≤ PP.asIdeal) :
    GlobalTheory.Grid.princGL β I ≤ princAt β PP := by
  intro x hx
  obtain ⟨y, rfl, hy⟩ := GlobalTheory.Grid.mem_princGL.1 (GlobalTheory.Grid.princGL_mono β h hx)
  refine mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  have h0 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hy i j), map_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem congLev_le_Kg [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) {I : Ideal (𝓞 E)} {T : Finset (Pl E)}
    (h : ∀ PP ∈ T, I ≤ PP.asIdeal) : congLev hc J Λ I ≤ Kg hc J β T := by
  rw [← GlobalTheory.ColMeas.princ_eq_congLev hc J hfr I]
  rintro x ⟨h1, h2⟩
  refine ⟨⟨h1, ?_⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => princGL_le_princAt β (h PP hP) h2⟩
  obtain ⟨y, e, -⟩ := GlobalTheory.Grid.mem_princGL.1 h2
  exact ⟨y, e⟩

end General

variable {D : D7} {T : Type}

theorem g_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem levRow_sub {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) :
    (levRow L : Set (GA D (Yc D 0))) ⊆ levS _ (L.βY 0) (L.dat0 L.triv) := by
  rintro k ⟨hk1, hk2⟩
  obtain ⟨c, hfr, -⟩ := hL.βY 0 (by have := D.R.two_le_m; omega)
  refine ⟨hk1, Kg_le_lev (T := L.Pg) (D := L.dat0 L.triv) subset_rfl (Finset.empty_subset _)
    (congLev_le_Kg _ _ hfr (fun PP hP => ?_) hk2)⟩
  obtain ⟨l, hl⟩ := (hL.Pg PP).1 hP
  have hg := g_mem hl
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
  fin_cases l
  · exact Ideal.mul_mem_right _ _ hg
  · exact Ideal.mul_mem_left _ _ hg

theorem principalRowLevelCharacter_trivial (L : LevCh D T) (k : GA D (Yc D 0)) : Lev.levChi _ (L.βY 0) (L.dat0 L.triv) k = 1 := by
  have h : levFn (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k) = 1 := by
    have h1 : ext1 (L.dat0 L.triv).P.H (L.dat0 L.triv).P.chi (rTup (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k)) = 1 :=
      Lev.subgroupCharExtension_one_apply _ _
    unfold levFn
    rw [h1]
    simp [LevCh.dat0, Lev.datY]
  unfold Lev.levChi
  rw [h, Units.val_one]

end GlobalTheory.SepRows.Good

theorem GlobalTheory.SepRows.goodRows : GoodRows := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R hL t ht
  rw [mem_multT, LinearEquiv.symm_apply_apply]
  refine Submodule.span_mono (fun U hU => ?_) (goodPart_le _ _ _ _ _ ht)
  exact ⟨hU.aut, hU.cusp, fun v k hk g => by
    rw [hU.lev v k (Good.levRow_sub hL hk) g, Good.principalRowLevelCharacter_trivial]; rfl, hU.equiv, hU.cont⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hθall⟩ := h
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, hmall⟩ := hAall A hA
  have e := hmall m hm
  have e' := ((h'.2.2 θ hθ).2 A hA).2 m hm
  have hμ' := h'.1
  have hB : ∀ ρ : D.what₂.Tau, ∃ B : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2),
      MeasurableSet B ∧ m ρ B ≠ 0 ∧ m ρ B ≠ ⊤ := by
    intro ρ
    obtain ⟨j1, j2, j3, -, j5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    haveI := hg ρ (m ρ) (hm ρ)
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
    exact ⟨C, hC.measurableSet, (by first | exact (Measure.measure_pos_of_mem_nhds (m ρ) hC1).ne' | exact (measure_pos_of_nonempty_interior (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'), hC.measure_lt_top.ne⟩
  choose B hBm hB0 hBt using hB
  set S := {h : GA D V | Lev.finE V h ∈ K ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hS : μ S = ∏ ρ, m ρ (B ρ) := e B hBm
  have hS' : μ' S = ∏ ρ, m ρ (B ρ) := e' B hBm
  have hp0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  have hpt : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hBt ρ
  have hc := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hcS : μ' S = (Measure.haarScalarFactor μ' μ : ENNReal) * μ S := by
    conv_lhs => rw [hc]
    rfl
  rw [hS, hS'] at hcS
  have hc1 : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hp0 hpt).1 (hcS.symm.trans (one_mul _).symm)
    exact this
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  intro D T L sc G M M' X K h h'
  unfold GlobalTheory.FunObj.Vol.IsAt at h h'
  split_ifs at h h'
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1

end GlobalTheory.HaarNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFiniteRationalRealGaussian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTrans

theorem entry_tr (zz xx : ℂ) (r : ℝ) :
    -(Real.pi * Complex.I) * (-((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ (zz + xx) * -xx)).re : ℝ) : ℂ)) +
      -((Real.pi * r : ℝ) : ℂ) * ((‖zz + xx‖ ^ 2 : ℝ) : ℂ) =
    -((Real.pi * r : ℝ) : ℂ) * ((‖zz‖ ^ 2 : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * (2 * (r : ℂ) * (zz * starRingEnd ℂ xx)) - (Real.pi : ℂ) * (2 * (r : ℂ) * (xx * starRingEnd ℂ xx)) / 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem heisO_finRat_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hf Φ hΦ M X hX w hw
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨z, rfl⟩ : ∃ z, GlobalTheory.FockCompare.iotaW σ T S z = w := ⟨_, hch.iota_pi hw⟩
  have e : GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T M =
      ratW T S M + GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M) := by
    rw [GlobalTheory.VacUnique.ratW_eq hch, AddMonoidHom.map_sub]; abel
  show ψ (symplOH S T _ (GlobalTheory.VacUnique.finRat S T M)) * f (_ + GlobalTheory.VacUnique.finRat S T M) = _
  rw [GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T M) hw, AddChar.map_zero_eq_one, one_mul, e,
    hf.quasi, AddChar.map_neg_eq_inv, GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ hθ hψ S T _ _ (Or.inr (hch.real_iota T S _)),
    GlobalTheory.VacUnique.piW_ratW hθ, hch.pi_iota, ← Complex.exp_neg,
    hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO]
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) with hZ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M)) = Z + X := by
    rw [hZ, GlobalTheory.ThetaLawOF.zCo_iota hch, GlobalTheory.ThetaLawOF.zCo_iota hch, hX]; funext τ a b
    show ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) - Matrix.of (GlobalTheory.VacUnique.infRat S T M τ)) * GlobalTheory.FockPos.frAt frS τ) a b = _
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact sub_eq_add_neg _ _
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T M) (z - GlobalTheory.VacUnique.infRat S T M) =
      ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re := by
    rw [GlobalTheory.ThetaLawOF.omO_frame frS frT hS hT, ← hz2, GlobalTheory.ThetaLawOF.zCo_iota hch]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX]
    simp only [neg_neg]
  rw [hz2, hom]
  have kE : Complex.exp (-(-(Real.pi * Complex.I) * ((∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re : ℝ) : ℂ))) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry_tr (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    simp only [Pi.add_apply] at h ⊢
    push_cast at h ⊢
    linear_combination h
  rw [← mul_assoc, kE]
  ring

end GlobalTheory.MovedTrans

end
end

