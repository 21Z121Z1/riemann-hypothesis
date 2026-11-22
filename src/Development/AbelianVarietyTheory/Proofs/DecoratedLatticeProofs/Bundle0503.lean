import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsBuiltAndNot
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumFrame
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.CoreIdele

variable {D : D7}

theorem card_eq_of_inv {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (b : Matrix m n k) (b' : Matrix n m k) (h : b * b' = 1) (h' : b' * b = 1) : Fintype.card n = Fintype.card m := by
  have h1 : Fintype.card m ≤ Fintype.card n := by
    have := Matrix.rank_mul_le_left b b'
    rw [h, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b)
  have h2 : Fintype.card n ≤ Fintype.card m := by
    have := Matrix.rank_mul_le_left b' b
    rw [h', Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b')
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sumFrame' (p : SplitPt D k) {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p A n) :
    ∃ β₀ : Frame p S (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hr : r ⬝ᵥ ζ = 1 := by
    simp only [r]
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let bE : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (o.iB *ᵥ ζ))
  let bE' : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (r ᵥ* o.qB))
  have h1 : bE' * bE = 1 := by
    simp only [bE, bE']
    rw [fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    congr 1
    · exact o.qA_iA
    · rw [← replicateCol_mulVec, Matrix.mulVec_mulVec, o.qA_iB, Matrix.zero_mulVec]; rfl
    · rw [← replicateRow_vecMul, Matrix.vecMul_vecMul, show o.qB * o.iA = 0 from o.symm.qA_iB, Matrix.vecMul_zero]; rfl
    · ext i j
      rw [replicateRow_mul_replicateCol_apply, dotProduct_mulVec, Matrix.vecMul_vecMul,
        show o.qB * o.iB = 1 from o.symm.qA_iA, Matrix.vecMul_one, hr, Subsingleton.elim i j, Matrix.one_apply_eq]
  have hn : Fintype.card n = A.rank := by simpa using card_eq_of_inv β.b β.b' β.bb' β.b'b
  let X : Matrix (Fin A.rank ⊕ Fin 1) (n ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (n ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have hX : X' * X = 1 := by
    simp only [X, X', fromBlocks_multiply, β.b'b]; simp
  have g1 : (X' * bE'.map f) * (bE.map f * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bE'.map f), ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, hX]
  have hc : Fintype.card (Fin S.rank) = Fintype.card (n ⊕ Fin 1) := by
    have := o.rank_add; have := hζ.1
    simp only [Fintype.card_fin, Fintype.card_sum, hn]; omega
  have g2 : (bE.map f * X) * (X' * bE'.map f) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).2 g1
  obtain ⟨β₀, h₀⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 S (n ⊕ Fin 1) _ _ g2 g1
  refine ⟨β₀, ?_⟩
  rw [IsSumFrame, h₀]
  simp only [bE, X, fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  ext i (j | j) <;> rfl

theorem line_of_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (v : Pl D) (ho : OrthAt o M LA LL v) (a : AE D) :
    a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a • ratV ζ ∈ latV L LL (· = v) := by
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.FinPl.CoreIdele

theorem GlobalTheory.FinPl.CoreIdele.lineLat_idele : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ m : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a ∈ intAt D (· = x)) → ∃ LL : Lat L, IsSelfDualC L LL ∧ ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP L ζ hζ m hm
  set h := star ζ ⬝ᵥ L.gram *ᵥ ζ with hhdef
  have hh : star h = h := by
    have hG : ∀ i j, star (L.gram i j) = L.gram j i := fun i j => by
      have := congrFun (congrFun (gram_conjTranspose L) j) i
      simpa [Matrix.conjTranspose_apply] using this
    have e : star (star ζ ⬝ᵥ L.gram *ᵥ ζ) = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hG]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    exact e
  obtain ⟨m', hoff, hon⟩ := GlobalTheory.T.exists_idele_change_finitely_many_split_places D k ι p I P hP h hζ.2 hh m
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.T.exists_fractionalIdeal_of_hermIdele D m'
  have key : ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by
    intro x hx a ha
    have h1 : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
    have h2 := (hoff x hx _ h1).1
    rw [← mul_assoc (m : AE D), Units.mul_inv, one_mul] at h2
    calc ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m'⁻¹ : (AE D)ˣ) : AE D) * ((m' : AE D) * (((m⁻¹ : (AE D)ˣ) : AE D) * a)) := by
          rw [h2]
      _ = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hloc : ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔
      (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
    intro x a ha
    by_cases hx : P x
    · exact hon x hx a ha
    · have h1 : incA D h * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
      have h2 : cA D (m : AE D) * (incA D h * a) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ h1
      have e : (m' : AE D) * cA D (m' : AE D) * incA D h * a = (m : AE D) * cA D (m : AE D) * incA D h * a := by
        rw [mul_assoc, mul_assoc, (hoff x hx _ h1).2, (hoff x hx _ h2).1, ← mul_assoc, ← mul_assoc]
      rw [e]
      exact hm x hx a ha
  have hsd := GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators D h 𝔞 m' h𝔞 hloc
  have hζ0 : ζ ≠ 0 := fun e => hζ.2 (by rw [e]; simp)
  refine ⟨GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 𝔞, GlobalTheory.SeeSaw.LiftModel.isSelfDualC_lineLat D L ζ hζ 𝔞 hsd, fun x hx a ha => ?_⟩
  rw [GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ0 𝔞 x a ha, h𝔞 x a ha, key x hx a ha]

open GlobalTheory.FinPl.CoreIdele GlobalTheory.SeeSaw.CoreGlue in

theorem GlobalTheory.FinPl.CoreIdele.exists_core : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (β : ∀ i, Frame (p i) B.A n) (Q : ι → Pair k n) (LA : Lat B.A), IsSelfDualC B.A LA → (∀ i, (β i).IsLat LA (Q i).lat) → (∀ i, valuation k ((p i).pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)) → ∀ m : (AE D)ˣ, (∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * a ∈ intAt D (· = x)) → (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a ∈ intAt D (· = x)) → ∃ (M : Lat B.V₀) (β₀ : ∀ i, Frame (p i) B.V₀ (n ⊕ Fin 1)), IsSelfDualC B.V₀ M ∧ (∀ i, GluedCore B M q (β i) (β₀ i) (Q i)) ∧ (∀ x, ¬ P x → ∃ LL : Lat B.L, IsSelfDualC B.L LL ∧ OrthAt B.o M LA LL x ∧ ∀ a ∈ idAt D (· = x), a • ratV B.ζ ∈ latV B.L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ x, ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP q n _ _ ρ B β Q LA hLA _ hnorm m hmP hmoff
  obtain ⟨LL, hLL, hline⟩ := lineLat_idele D k ι p I P hP B.L B.ζ B.line m hmoff
  obtain ⟨M₁, hM₁, horth⟩ := exists_orthSum B.o hLA hLL
  have frames : ∀ i, ∃ β₀ : Frame (p i) B.V₀ (n ⊕ Fin 1), IsSumFrame B.o B.ζ (β i) β₀ :=
    fun i => exists_sumFrame' (p i) B.o B.line (β i)
  choose β₀ hβ₀ using frames
  obtain ⟨M, hM, hlat, hoff⟩ := exists_modify hP.inj β₀ (fun i => gluedS q 1 (Q i).ker (Q i).vec)
    (fun i => by haveI := (Q i).ker_isLat; infer_instance) hM₁ I
  have glued : ∀ i, GluedCore B M q (β i) (β₀ i) (Q i) := fun i =>
    ⟨hP.unit i, hβ₀ i, hnorm i, hlat i (hP.all i)⟩
  have offP : ∀ x, ¬ P x → ∀ i, x ≠ (p i).v := fun x hx i e => hx ((hP.mem x).2 ⟨i, e⟩)
  have horthM : ∀ x, ¬ P x → OrthAt B.o M LA LL x := fun x hx y => by
    rw [hoff x (offP x hx)]
    exact horth x y
  refine ⟨M, β₀, hM, glued, fun x hx => ⟨LL, hLL, horthM x hx, hline x hx⟩, fun x a ha => ?_⟩
  by_cases hx : P x
  · obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    rw [line_of_glued hM (glued i) ha]
    have hma : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_left _ _ ha
    have := hmP _ hx _ hma
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
  · rw [line_of_orth B.o B.ζ M LA LL x (horthM x hx) a]
    exact hline x hx a ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.StdOff

section Gen

open GlobalTheory.FinPl GlobalTheory.FinPl.AlmostAll GlobalTheory.FinPl.AeUnit

variable {D : D7}

theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ ((N : D.host.E) * c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hv' : ((N : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by rwa [Int.cast_natCast]
  have hN : N ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have hNF : ((N : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨(N : ℤ) • c, by rw [zsmul_eq_mul, Int.cast_natCast]; exact hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

theorem latA_eq_latV_of {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * (N : D.host.E)) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact hvN (by simp)
  have hM : M ≠ 0 := by
    rintro rfl
    exact hvM (by simp)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [tmul_eq hN, ← mul_assoc, mul_comm (N : D.host.E) a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [tmul_eq hM, one_mul]

theorem notMem_of_coprime {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : ℕ} (h : a.Coprime b) (hb : (b : R) ∈ P) :
    (a : R) ∉ P := fun ha => by
  obtain ⟨x, y, hxy⟩ : IsCoprime (a : R) (b : R) := Nat.Coprime.cast h
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAA_of (p : SplitPt D k) {l : ℕ} (hl : l.Prime) (hv : (l : 𝓞 D.host.F) ∈ p.v.asIdeal)
    (hq : (D.host.QS * D.host.q).Coprime l) (hd : D.host.d.Coprime l) (hc : (Ideal.absNorm D.host.ccK).Coprime l) : p.UnitAA := by
  have hb : (Ideal.absNorm D.host.𝔟).Coprime l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd, GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl, ← hl.coprime_iff_not_dvd]
    exact hq.symm
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hd4 : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs2 := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    exact hd0 (neg_eq_zero.1 hs2.symm)
  have hsi : IsIntegral ℤ D.host.sqrtMinusD := IsIntegral.of_pow two_pos (by rw [hs2]; exact (isIntegral_natCast _).neg)
  refine ⟨fun a ha => ⟨incA_mul_mem_intAt (N := Ideal.absNorm D.host.ccK * D.host.d)
    (notMem_of_coprime p.v.isPrime (hc.mul_left hd) hv) ?_ a ha, incA_mul_mem_intAt (N := 1)
    (notMem_of_coprime p.v.isPrime (Nat.coprime_one_left l) hv) ?_ a ha⟩,
    latA_eq_latV_of (notMem_of_coprime p.v.isPrime hb hv) (notMem_of_coprime p.v.isPrime hc hv)
      (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · convert hsi using 1
    unfold Host.xi0
    push_cast
    field_simp
    linear_combination -hs2
  · have : ((1 : ℕ) : D.host.E) * D.host.xi0⁻¹ = -((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) := by
      unfold Host.xi0
      rw [Nat.cast_one, one_mul, inv_div, div_neg, div_one]
    rw [this]
    exact ((isIntegral_natCast _).mul hsi).neg

theorem mxAt_of_half (q : SplitPt D k) {m n : ℕ} {w : Mx D m n} (h : IsHalf (q.e + cA D q.e) w) : MxAt (· = q.v) w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff, ← h2]
  exact h i j

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  have h1 : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have h2 : (p.e + cA D p.e) * p.sec a = p.sec a := by
    rw [← h1, ← mul_assoc, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
  exact mxAt_of_half p (m := 1) (n := 1) (w := Matrix.of fun _ _ => p.sec a) (fun _ _ => h2) 0 0

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) : idAt D P ≤ idAt D Q := fun _ ha =>
  Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 ha).1, (Submodule.mem_iInf _).2 fun u =>
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨u.1, fun hu => u.2 (h _ hu)⟩⟩

theorem mem_latV_int {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (v : Pl D) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) :=
  GlobalTheory.FinPl.Model.mem_latV_std S L (fun x => (hL x).trans (forall_congr' fun i =>
    ⟨fun h => ⟨⟨x i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩)) v y

def intLat (S : HSp D) : Lat S := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

end Gen

section Loc

open GlobalTheory.LatPair IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section Level

open GlobalTheory.FinPl

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end Level

theorem exists_vT_over {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (v' : HeightOneSpectrum (𝓞 X.F))
    (hT : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v'.asIdeal) : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v' := by
  have hinj : Function.Injective (algebraMap (𝓞 X.F) (𝓞 X.E)) := by
    intro x y e
    apply RingOfIntegers.ext
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) e
    simpa using this
  haveI : Algebra.IsIntegral (𝓞 X.F) (𝓞 X.E) := inferInstance
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 X.E) v'.asIdeal ⊥ (by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQ
    exact v'.ne_bot hQ.symm
  let QQ : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQp, hQ0⟩
  have hTQ : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ QQ.asIdeal := by
    have : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) Q := hQ ▸ hT
    simpa using this
  rw [← hPr.piT_norm u] at hTQ
  rcases hQp.mem_or_mem hTQ with hπ | hπ
  · exact ⟨QQ, (GlobalTheory.MuOffMove.mem_vT hPr u QQ).2 hπ, HeightOneSpectrum.ext hQ⟩
  · refine ⟨Formalism.L2.Col.conjPrime₂ QQ, (GlobalTheory.MuOffMove.mem_vT hPr u _).2 ((Formalism.L2.Col.mem_conjP _ _).2 ?_), HeightOneSpectrum.ext ?_⟩
    · exact hπ
    · show Ideal.under _ _ = _
      rw [GlobalTheory.MuOffMove.under_conjP hX]
      exact hQ

end GlobalTheory.SeeSaw.StdOff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameLatticeMembershipCriterion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

theorem wShape_of_besFrame : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : Lat (d.st 0).V), (∀ y : GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k, (fun r => G.q.sec (((G.FY 0 (G.s + 1) (zero_add _)).β *ᵥ y) r)) ∈ latV (d.st 0).V L (· = G.q.v) ↔ (∀ a, y (Sum.inl a) ∈ 𝒪[G.k]) ∧ ∀ i : Fin (G.s + 1), ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k]) → WShape G.q (d.bes 0 ρ h0).d (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (d.x 0).L := by
  intro D u d τ PP G ρ h0 L hL
  obtain ⟨hc, hA, he, hz, he'⟩ := G.bes 0 ρ h0 (G.s + 1) (zero_add _)
  intro x x' t y
  have hsc : valuation G.k (G.sc 0) = 1 := G.sc_unit 0
  have hxi : valuation G.k (GlobalTheory.LocMod.ofSplit G.q).xi = 1 := GlobalTheory.SeeSaw.CoreGlue.valuation_xi_zero_eq_one G.q G.unit
  have hhz : valuation G.k ((GlobalTheory.LocMod.ofSplit G.q).hz (d.B 0 ρ h0)) = 1 := G.hz_unit 0 ρ h0
  set cE : Fin ρ → G.k := fun i => G.sc 0 * (GlobalTheory.LocMod.ofSplit G.q).xi ^ (ρ - i.1) with hcE
  set cE' : Fin ρ → G.k := fun i => G.sc 0 * (-(GlobalTheory.LocMod.ofSplit G.q).hz (d.B 0 ρ h0) / (GlobalTheory.LocMod.ofSplit G.q).xi) *
    (-1 / (GlobalTheory.LocMod.ofSplit G.q).xi) ^ (ρ - 1 - i.1) with hcE'
  have vE : ∀ i, valuation G.k (cE i) = 1 := fun i => by simp [cE, map_pow, hsc, hxi]
  have vE' : ∀ i, valuation G.k (cE' i) = 1 := fun i => by
    simp [cE', map_pow, map_div₀, Valuation.map_neg, hsc, hxi, hhz]
  have nz : ∀ {c : G.k}, valuation G.k c = 1 → c ≠ 0 := fun h h0 => by simp [h0] at h
  have he2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE i * G.q.pr (incA D ((d.bes 0 ρ h0).d.e r i)) := he
  have hz2 : ∀ (j : Fin (G.s + 1)), j.1 = ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      G.sc 0 * G.q.pr (incA D (((d.bes 0 ρ h0).d.i₀ *ᵥ vecB (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ) r)) := hz
  have he'2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE' i * G.q.pr (incA D ((d.bes 0 ρ h0).d.e' r i)) := he'
  have hA2 : ∀ r a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) =
      (atW G.q ((d.bes 0 ρ h0).d.i₀ * (d.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) r a := hA
  let Yr : Fin (G.s + 1) → G.k := fun j => if h : j.1 < ρ then x ⟨j.1, h⟩ / cE ⟨j.1, h⟩ else if j.1 = ρ then t / G.sc 0
      else if h' : 2 * ρ - j.1 < ρ then x' ⟨2 * ρ - j.1, h'⟩ / cE' ⟨2 * ρ - j.1, h'⟩ else 0
  let Y : StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k := Sum.elim ((G.FX 0 (by omega)).γ *ᵥ y) Yr
  have YrE : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → Yr j = x i / cE i := by
    intro i j hj
    have h : j.1 < ρ := hj ▸ i.2
    have : (⟨j.1, h⟩ : Fin ρ) = i := Fin.ext hj
    simp only [Yr, dif_pos h, this]
  have YrZ : ∀ (j : Fin (G.s + 1)), j.1 = ρ → Yr j = t / G.sc 0 := by
    intro j hj
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_pos hj]
  have YrE' : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → Yr j = x' i / cE' i := by
    intro i j hj
    have h : 2 * ρ - j.1 < ρ := by omega
    have : (⟨2 * ρ - j.1, h⟩ : Fin ρ) = i := Fin.ext (by simp; omega)
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_neg (show ¬ j.1 = ρ by omega), dif_pos h, this]
  have hlat : (∀ a, Y (Sum.inl a) ∈ 𝒪[G.k]) ↔ (fun r => G.q.sec (y r)) ∈ latV (D.sp.X 0) (d.x 0).L (· = G.q.v) := by
    have h := G.latX 0 (by omega) ((G.FX 0 (by omega)).γ *ᵥ y)
    rw [Matrix.mulVec_mulVec, (G.FX 0 (by omega)).βγ, Matrix.one_mulVec] at h
    exact h
  refine Iff.trans (Eq.to_iff ?_) ((hL Y).trans ?_)
  · congr 1
    funext r
    congr 1
    symm
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [Y, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) * ((G.FX 0 (by omega)).γ *ᵥ y) a =
        (atW G.q ((d.bes 0 ρ h0).d.i₀ * (d.bes 0 ρ h0).o.iA) *ᵥ y) r := by
      calc _ = ((atW G.q ((d.bes 0 ρ h0).d.i₀ * (d.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) *ᵥ
            ((G.FX 0 (by omega)).γ *ᵥ y)) r := by simp only [hA2]; rfl
        _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, (G.FX 0 (by omega)).βγ, Matrix.mul_one]
    have h2 := sum_fin_two_mul_add_one hc (fun j => (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) * Yr j)
      (fun i => G.q.pr (incA D ((d.bes 0 ρ h0).d.e r i)) * x i) (fun i => G.q.pr (incA D ((d.bes 0 ρ h0).d.e' r i)) * x' i)
      (G.q.pr (incA D (((d.bes 0 ρ h0).d.i₀ *ᵥ vecB (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ) r)) * t)
      (fun i j hj => by beta_reduce; rw [he2 i j hj r, YrE i j hj, mul_mul_div_cancel_left' (nz (vE i))])
      (fun j hj => by beta_reduce; rw [hz2 j hj r, YrZ j hj, mul_mul_div_cancel_left' (nz hsc)])
      (fun i j hj => by beta_reduce; rw [he'2 i j hj r, YrE' i j hj, mul_mul_div_cancel_left' (nz (vE' i))])
    rw [h1, h2]
    have hm : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.map_one _ (map_zero G.q.pr) (map_one G.q.pr),
      Matrix.one_mulVec]
    simp only [Matrix.mulVec, dotProduct, atW, Matrix.map_apply]
    ring
  · have hinr : (∀ j : Fin (G.s + 1), (((G.S.ϖ : G.kˣ) : G.k) ^ (j.1 + 1))⁻¹ * Yr j ∈ 𝒪[G.k]) ↔
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (a.1 + 1))⁻¹ * x a ∈ 𝒪[G.k]) ∧
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - a.1 + 1))⁻¹ * x' a ∈ 𝒪[G.k]) ∧
        (((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹ * t ∈ 𝒪[G.k] := by
      constructor
      · intro h
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · have := h ⟨a.1, by omega⟩
          rwa [YrE a _ rfl, mul_div_mem_integer_iff (vE a)] at this
        · have := h ⟨2 * ρ - a.1, by omega⟩
          rwa [YrE' a _ (by simp only; omega), mul_div_mem_integer_iff (vE' a)] at this
        · have := h ⟨ρ, by omega⟩
          rwa [YrZ _ rfl, mul_div_mem_integer_iff hsc] at this
      · rintro ⟨h1, h2, h3⟩ j
        rcases lt_trichotomy j.1 ρ with hj | hj | hj
        · rw [YrE ⟨j.1, hj⟩ j rfl, mul_div_mem_integer_iff (vE _)]
          exact h1 ⟨j.1, hj⟩
        · rw [YrZ j hj, mul_div_mem_integer_iff hsc, hj]
          exact h3
        · have hi : 2 * ρ - j.1 < ρ := by omega
          rw [YrE' ⟨2 * ρ - j.1, hi⟩ j (by simp only; omega), mul_div_mem_integer_iff (vE' _)]
          have h4 := h2 ⟨2 * ρ - j.1, hi⟩
          have h5 : 2 * ρ - (2 * ρ - j.1) = j.1 := by omega
          simp only [h5] at h4
          exact h4
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨a, b, c⟩ := hinr.1 hr
      exact ⟨a, b, c, hlat.1 hl⟩
    · rintro ⟨a, b, c, l⟩
      exact ⟨hlat.2 l, hinr.2 ⟨a, b, c⟩⟩

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineProjection_mem_splitCoreCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  first | exact @GlobalTheory.LineProj.lineProj_mem | exact GlobalTheory.LineProj.lineProj_mem | (intros; apply GlobalTheory.LineProj.lineProj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_equation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } (PP.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.SplitAtPlaces.splitAt_places | exact GlobalTheory.SplitAtPlaces.splitAt_places | (intros; apply GlobalTheory.SplitAtPlaces.splitAt_places <;> assumption)
end

