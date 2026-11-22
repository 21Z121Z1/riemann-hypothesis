import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rowLevel_of_reduction_mem_levelGroup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  first | exact @GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp | exact GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp | (intros; apply GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunctionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  first | exact @GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | exact GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | (intros; apply GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMapStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minorProductPairing_determined_by_canonicalMap : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  first | exact @GlobalTheory.KForm.WWUnique.ww_unique | exact GlobalTheory.KForm.WWUnique.ww_unique | (intros; apply GlobalTheory.KForm.WWUnique.ww_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  first | exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic | exact GlobalTheory.Mem.Col2.DnAdel.move_down_adelic | (intros; apply GlobalTheory.Mem.Col2.DnAdel.move_down_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroForcedContentPlacesAgreeOverEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl

theorem resCharW_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl w) = Examples₂.PlacesToy.resCharW w := by
  have hm : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) (Examples₂.PlacesToy.resCharW_mem w)
    rwa [map_natCast] at this
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem FTypeG_of_kapDef {D : D7} (hk : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    FTypeG D j = -(∑ τ : D.what₂.Tau, ((∑ i : Fin (D.R.sigW j).1, |((DV.aPlusQ D j τ i : ℚ) : ℝ)|) +
      ∑ c : Fin (D.R.sigW j).2, |((DV.aMinusQ D j τ c : ℚ) : ℝ)|)) / 2 := by
  unfold FTypeG fockDeg
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hb, hs⟩ := hk j h1 h2 τ
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    norm_cast
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [show ((DV.aMinusQ D j τ c : ℚ) : ℝ) = -((D.what₂.kaSmall j τ c : ℚ) : ℝ) by rw [hs c]; push_cast; ring, abs_neg]
    norm_cast

theorem mem_W1F_forced_iff (s : Scale) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    (v : HeightOneSpectrum (𝓞 B.LL)) :
    v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K s (w.D Z)) ↔
      ∃ j : ℕ, j < B.R.m ∧ FK s (w.D Z) (j + 1) (Examples₂.PlacesToy.resCharW v) ≠ 0 := by
  constructor
  · rintro ⟨j, y, hy, h⟩
    refine ⟨j.1, j.2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h
    · have e : F0K s (w.D Z) (Formalism.DivisionValues.conjPl v) j = FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW v) := by
        show FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl v)) = _
        rw [resCharW_conjPl]
      exact e ▸ h
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj⟩, v, Or.inl rfl, h⟩

theorem FK_enl (s : Scale) {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre)
    (hk : DV.KapDef (w.D Z)) (hk' : DV.KapDef (w'.D Z')) (j p : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    FK s (w.D Z) j p = FK s (w'.D Z') j p := by
  have h2' : j ≤ B'.R.m := by rw [h]; exact h2
  unfold FK
  rw [FTypeG_of_kapDef hk h1 h2, FTypeG_of_kapDef hk' h1 h2']
  clear hk hk'
  cases B'
  subst h
  rfl

theorem resCharW_of_below {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (v : HeightOneSpectrum (𝓞 B.LL))
    (v' : HeightOneSpectrum (𝓞 B'.LL)) (hB : Below (w.D Z) (w'.D Z') v v') :
    Examples₂.PlacesToy.resCharW v' = Examples₂.PlacesToy.resCharW v := by
  have he : (w.D Z).what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w.D Z).what₂.LL) : (w.D Z).what₂.LL) =
      (w'.D Z').what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w'.D Z').what₂.LL) : (w'.D Z').what₂.LL) := by
    simp only [map_natCast]
  have hm := (hB _ _ he).1 (Examples₂.PlacesToy.resCharW_mem v)
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem nonzeroForcedContentPlaces_agree_over_enlargement : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B')
    (w' : ColW B' f' T'), Enl B B' → ∀ (Z : w.Lt) (Z' : w'.Lt), DV.KapDef (w.D Z) → DV.KapDef (w'.D Z') →
    ∀ v v', Below (w.D Z) (w'.D Z') v v' →
      (v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)) ↔ v' ∈ R3.placesWithNonzeroContentOrConj (w'.D Z') (F0K K.s (w'.D Z'))) := by
  intro K B f T w B' f' T' w' hE Z Z' hk hk' v v' hB
  have hres := resCharW_of_below w w' Z Z' v v' hB
  have hm : B'.R.m = B.R.m := by rw [hE.1]
  refine (mem_W1F_forced_iff K.s w Z v).trans (Iff.trans ?_ (mem_W1F_forced_iff K.s w' Z' v').symm)
  rw [hm, hres]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [FK_enl K.s w w' Z Z' hE.1 hk hk' (j + 1) _ (Nat.succ_pos j) hj]

end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

theorem om_sizes_le_poR (f r L lE lh lN lhs lG lr ld rk ldeg : ℝ) (hf : 8 ≤ f) (hr : 62 ≤ r) (hL : 4 ≤ L)
    (hlf : Real.log f ≤ L) (hE0 : 0 ≤ lE) (hE : lE ≤ 2 * L)
    (hh : lh ≤ f * lE + 2 * f * Real.log (1 + f * lE)) (hN : lN ≤ 20 * L + 2) (hs0 : 0 ≤ lhs)
    (hs : lhs ≤ lh + 2 * f * lN) (hG : lG ≤ f * r ^ 2 * (18 * L + 2)) (hr' : lr ≤ lG + 24)
    (hd : ld ≤ 4 * L) (hk : rk ≤ 2 * f) (hdeg : ldeg ≤ 1 + L) :
    (ld + 20) + (ldeg + lhs) + lr + (ldeg + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L ∧
    (3 * ld + 20) + (lE + lN + lhs) + lr + (lE + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L)) := Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L) := Real.log_mul hf0.ne' (by positivity)
  have h3 : Real.log (3 * L) ≤ 3 * L - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2) := mul_le_mul_of_nonneg_left hN (by positivity)
  have h8 : 4 * f ≤ f * L := by nlinarith
  have h9 : lhs ≤ 51 * (f * L) := by nlinarith
  have h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))
  have h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h12 : 8 * (f * L) ≤ f * (f * L) := mul_le_mul_of_nonneg_right hf (by positivity)
  have h13 : f * (f * L) = f ^ 2 * L := by ring
  constructor <;> nlinarith

theorem sz_Om_poR : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  intro hR P δ L hL
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  obtain ⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩ := exists_hostK P.R P.host
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
  have hrd : lE ≤ 2 * L := hlE' ▸ hL.rd

  have hd : Real.log (P.host.d : ℝ) ≤ 4 * L := by
    obtain ⟨_, -, h⟩ := sz_mono_and_of_le.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2, hKd] at h'
    push_cast at h'
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h'
    linarith

  have hM' := GlobalTheory.T.field_datum_size_log_discriminant hR P δ
  obtain ⟨hdeg_le, hray⟩ := GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)
  have hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P)) :=
    sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))
  have hV : Sz δ.V _ _ := GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots P.host.E P.host.φ₀ δ.hstar δ.hstar_pos
  have hall := sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV
  change Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _

  obtain ⟨hG, -, hf8, -⟩ := roots_sizes P L hL
  have hf0 : (0 : ℝ) < P.R.f := by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)
  have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
  rw [← hlE'] at hcl
  have hh0 : 0 < classNumber P.host.E := classNumber_pos _

  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := P.host.pde_prime.pos
  have hp' := P.host.pde'_prime.pos
  have hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2 := by
    have e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde +
        Real.log P.host.pde' := by
      simp only [modulus]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    have := hL.g 0
    have := hL.g 1
    have := hL.p
    rw [e]; linarith [this.1, this.2]

  have hs0 : 0 ≤ Real.log (δ.hstar : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ) := by
    have h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E := by
      exact_mod_cast hdeg_le
    have h2 := Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg] at h2
    push_cast at h2
    linarith

  have hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24 := by
    have hc := P.restRowsFiniteGroupCard_pos
    have h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
    have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5 := by
      rw [show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith

  have hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f := by
    have : NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E := by
      rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
    rw [hdeg] at this
    exact_mod_cast this
  have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
    rw [hdeg]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have := hL.deg
    linarith
  have hnum := om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ))
    (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ))
    (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host.E)) (by exact_mod_cast hf8)
    (by exact_mod_cast hL.rank) hL.len hL.deg hlE0 hrd hcl hN hs0 hs hG hr hd hk d1
  refine sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_
  · unfold poR; exact hnum.1
  · unfold poR; exact hnum.2

end GlobalTheory.FieldSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_congruence_subgroup_preserves_principal_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), ∃ N : ℕ, 0 < N ∧ ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ J v S.Lb → (∀ y ∈ Formalism.L2.Herm.locL v S.Lb, ∃ z ∈ Formalism.L2.Herm.locL v S.Lb, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (N : E ⊗[F] v.adicCompletion F) • z) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.OpenPrinc.open_princ | exact GlobalTheory.OpenPrinc.open_princ | (intros; apply GlobalTheory.OpenPrinc.open_princ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersForcedContentEqScaleAtResidueCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forcedContent_eq_scale_at_residueChar : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl), Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  first | exact @GlobalTheory.Mem.Top.Bl.Fval_eq_FK | exact GlobalTheory.Mem.Top.Bl.Fval_eq_FK | (intros; apply GlobalTheory.Mem.Top.Bl.Fval_eq_FK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.NearCong

open WithZero

theorem mul_cong {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {n : ℕ} (N : ℕ) (A C : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r s, v ((A - 1) r s) ≤ exp (-(N : ℤ))) (hC : ∀ r s, v ((C - 1) r s) ≤ exp (-(N : ℤ))) :
    ∀ r s, v ((A * C - 1) r s) ≤ exp (-(N : ℤ)) := by
  intro r s
  have he : exp (-(N : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  calc v ((A - 1) r k) * v ((C - 1) k s) ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hA r k) ((hC k s).trans he)
    _ = exp (-(N : ℤ)) := mul_one _

section Rat
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_inv_mul (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hC : CongE P c g' g) : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) ∈ Formalism.L2.Col.stdAt E n P := by
  intro x hx
  have hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P := inv_mem hg
  have e1 : (g⁻¹ * g') x = g⁻¹ (g' x) := rfl
  have e2 : g⁻¹ (g x) = x := by
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x)) := by
    rw [map_smul, map_sub, e1, e2]
  rw [e]
  exact (hgi _).2 (hC x hx)

theorem val_entry (P : HeightOneSpectrum (𝓞 E)) (hq : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)) (c : ℕ)
    (h : Sp E n ≃ₗ[E] Sp E n)
    (hh : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (h x - x) ∈ Formalism.L2.Col.stdAt E n P) (r s : Fin n) :
    P.valuation E (LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s) ≤ exp (-(c : ℤ)) := by
  have hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.TwistRowType.mem_stdAt]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact (GlobalTheory.TwistRowType.intSub P).one_mem
    · exact (GlobalTheory.TwistRowType.intSub P).zero_mem
  have h1 := (GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r
  rw [GlobalTheory.UnramCompletion.intAt_iff] at h1
  rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq] at h1
  have e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0) := by
    rw [LinearMap.toMatrix'_apply, Matrix.one_apply]; rfl
  rw [e]
  generalize P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1
  have hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]; congr 1; simp
  rw [hE] at h1
  have hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1 := by rw [← exp_add]; simp
  calc y = (exp (-(c : ℤ)) * exp (c : ℤ)) * y := by rw [hm, one_mul]
    _ = exp (-(c : ℤ)) * (exp (c : ℤ) * y) := mul_assoc _ _ _
    _ ≤ exp (-(c : ℤ)) * 1 := mul_le_mul' le_rfl h1
    _ = exp (-(c : ℤ)) := mul_one _

end Rat

section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem vAlg' (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem adAt_ratA (P : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin n) E) (r s : Fin n) :
    adAt F P (((GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) :=
  adAt_inclE F P _

theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (c d : ℕ) (hcd : c ≤ d) (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : GlobalTheory.TwU.CongAt P d (x⁻¹ * GlobalTheory.TwU.ratA F (G g))) (hC : CongE P c g' g) :
    GlobalTheory.TwU.CongAt P c (x⁻¹ * GlobalTheory.TwU.ratA F (G g')) := by
  have hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ) := by
    rw [← vAlg', map_natCast]
    exact hq
  have e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) := by
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hiff] at h
  rw [hiff, e]
  have hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ)) := by rw [exp_le_exp]; omega
  have key := mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c
    ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    (fun r s => (h r s).trans hdc) (fun r s => ?_)
  · intro r s
    have := key r s
    rwa [← map_mul, ← Units.val_mul] at this
  · show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _
    rw [adAt_ratA, hG]
    have h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, ← map_sub, vAlg']
    exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s

end Core

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  intro B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢
  obtain ⟨hseam, hq, -⟩ := GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a 0 0 P 1
  have hiff := fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  rw [hseam] at hIn hiff ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC

end GlobalTheory.Mem.Col2.AdT.NearCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

theorem realPins3_realTOf : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (y : RealIn a.x Rc S), HEq (a.Zsc (zsOf t.r.z.R t.r.z.F)).F0 (F0K K.s (w.D Z)) → RealPins3 (realTOf y) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a Rc S y h
  rw [Pins3.realPins3_iff]

  have hr := t.r.z.twisted_places_eq_complex_side_of_eq_nonzero_index (F0K K.s (w.D Z)) t.exact.symm t.r.z.R.kap a.lam a.err a.Dc a.Sp a.Zsc 0 0 (eq_of_heq h)
  show ∀ v, v ∈ a.x.R.twPl ↔ (a.x.R.toCx3 a.x.F).W1 a.x.F.cr (a.x.R.num a.x.F 0 0) v
  clear y h

  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hr ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hr

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroupStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  first | exact @GlobalTheory.KerVal.prTC_val | exact GlobalTheory.KerVal.prTC_val | (intros; apply GlobalTheory.KerVal.prTC_val <;> assumption)
end

