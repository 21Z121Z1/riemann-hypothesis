import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocWeil.CompactPart

theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ Formalism.UG.Jpq p q * b = b * Formalism.UG.Jpq p q := by
  rw [← Matrix.fromBlocks_toBlocks b]
  generalize b.toBlocks₁₁ = a, b.toBlocks₁₂ = c, b.toBlocks₂₁ = d, b.toBlocks₂₂ = e
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, true_and, and_true]
  constructor
  · intro h
    have hc : c = 0 := by
      ext i j
      exact h (.inl i) (.inr j) (by simp [sameBlock])
    have hd : d = 0 := by
      ext i j
      exact h (.inr i) (.inl j) (by simp [sameBlock])
    simp [hc, hd]
  · rintro ⟨h1, h2⟩ x y hxy
    rcases x with i | i <;> rcases y with j | j
    · simp [sameBlock] at hxy
    · have := congrFun (congrFun h1 i) j
      simp only [Matrix.neg_apply] at this
      show c i j = 0
      linear_combination this / 2
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.neg_apply] at this
      show d i j = 0
      linear_combination -this / 2
    · simp [sameBlock] at hxy

theorem isKC_one {p q : ℕ} : IsKC (1 : Mat p q) := by
  rw [isKC_iff, Matrix.one_mul, Matrix.mul_one]

theorem isKC_mul {p q : ℕ} {a b : Mat p q} (ha : IsKC a) (hb : IsKC b) : IsKC (a * b) := by
  rw [isKC_iff] at *
  rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]

theorem isKC_inv {p q : ℕ} {a b : Mat p q} (ha : IsKC a) (h : a * b = 1) : IsKC b := by
  rw [isKC_iff] at *
  have h' : b * a = 1 := mul_eq_one_comm.1 h
  calc Formalism.UG.Jpq p q * b = b * a * Formalism.UG.Jpq p q * b := by rw [h', Matrix.one_mul]
    _ = b * Formalism.UG.Jpq p q * (a * b) := by
      rw [Matrix.mul_assoc b a, ← ha]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.mul_one]

variable {D : D7}

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem infMat_mul' (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * g') = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ g' := by
  rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]

theorem infMat_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V} (hk : k ∈ GfC V) :
    infMat D.sp.cm.sig V.gram θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_inv {V : HSp D} (hV : V.SigOK) {τ : D.what₂.Tau}
    {A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = gramAt D V τ) :
    ∃ B : Matrix (Fin V.rank) (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) ℂ, B * A = 1 ∧ A * B = 1 := by
  have hd : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := ((tauE D τ).map_det V.gram).symm
    rw [this, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (GlobalTheory.LocWCompare.gram_det_ne V)
  have h1 : ((gramAt D V τ)⁻¹ * (Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2)) * A = 1 := by
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ hd]
  have hc := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
  refine ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ ?_).1 h1⟩
  simp only [Fintype.card_fin, Fintype.card_sum] at hc ⊢
  omega

def kinf (θ : InfF D) {V : HSp D} (A : CptF V) (hV : V.SigOK)
    (hA : ∀ τ, (A τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A τ = gramAt D V τ) :
    Subgroup (GA D V) where
  carrier := {k | IsKinf θ V A k}
  one_mem' := ⟨one_mem _, fun τ => ⟨1, isKC_one, by
    rw [infMat_of_fin V _ (one_mem _), Matrix.one_mul, Matrix.mul_one]⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨mul_mem g1 h1, fun τ => ?_⟩
    obtain ⟨a, ha, ea⟩ := g2 τ
    obtain ⟨b, hb, eb⟩ := h2 τ
    refine ⟨a * b, isKC_mul ha hb, ?_⟩
    rw [infMat_mul', Matrix.mul_assoc, eb, ← Matrix.mul_assoc, ea, Matrix.mul_assoc]
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    refine ⟨inv_mem g1, fun τ => ?_⟩
    obtain ⟨a, ha, ea⟩ := g2 τ
    obtain ⟨B, hB, hB'⟩ := exists_inv hV (hA τ)
    refine ⟨A τ * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * B, isKC_inv ha ?_, ?_⟩
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ea, Matrix.mul_assoc (A τ), ← infMat_mul', mul_inv_cancel,
        infMat_of_fin V _ (one_mem _), Matrix.mul_one, hB']
    · rw [Matrix.mul_assoc, hB, Matrix.mul_one]

end GlobalTheory.LocWeil.CompactPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
      have h3 := mul_mem h2 h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
      exact h3
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

theorem toEAf_incA (D : D7) (x : D.host.E) : toEAf D (incA D x) = eToEAf D x := rfl

theorem eToEAf_int (D : D7) (x : 𝓞 D.host.E) :
    eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)

theorem conj_mem_at (D : D7) (e : AE D) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have hi : IsIntegral ℤ (D.sp.cm.sig (c : D.host.E)) :=
    (show IsIntegral ℤ (c : D.host.E) from c.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom
  have h3 := mul_mem h2 (eToEAf_int D ⟨_, hi⟩)
  rw [map_mul, toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  change D.sp.cm.sig a = ((n : 𝓞 D.host.E) : D.host.E)⁻¹ * D.sp.cm.sig (c : D.host.E)
  rw [hc', hcast, map_mul, map_natCast]
  field_simp

theorem conj_mem_intAf : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rintro D e P ⟨⟨es, hes, rfl⟩, -⟩ hP a ha
  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => conj_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

end GlobalTheory.IdemIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCf
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.TypeSumCtrl

def allWords {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) : List (List α) :=
  Nat.rec [[]] (fun _ T => [] :: T.flatMap fun l => (List.ofFn E).map fun X => X :: l) m

theorem allWords_zero {α : Type} {k : ℕ} (E : Fin k → α) : allWords E 0 = [[]] := rfl

theorem allWords_succ {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) :
    allWords E (m + 1) = [] :: (allWords E m).flatMap fun l => (List.ofFn E).map fun X => X :: l := rfl

theorem mem_allWords {α : Type} {k : ℕ} (E : Fin k → α) :
    ∀ (m : ℕ) (l : List α), l ∈ allWords E m ↔ l.length ≤ m ∧ ∀ X ∈ l, ∃ i, E i = X
  | 0, l => by
    cases l <;> simp [allWords_zero]
  | m + 1, [] => by simp [allWords_succ]
  | m + 1, X :: l => by
    simp only [allWords_succ, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_ofFn, List.length_cons,
      reduceCtorEq, false_or, List.cons.injEq, forall_eq_or_imp, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨l', h1, Y, h2, rfl, rfl⟩
      exact ⟨((mem_allWords E m _).1 h1).1, h2, ((mem_allWords E m _).1 h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨l, (mem_allWords E m _).2 ⟨h1, h3⟩, X, h2, rfl, rfl⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {k : ℕ}

def cf (E : Fin k → Mx n) (X : Mx n) : ℝ := ∑ i, |((X * (E i)ᴴ).trace).re|

theorem cf_nonneg (E : Fin k → Mx n) (X : Mx n) : 0 ≤ cf E X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_cf (E : Fin k → Mx n) : Continuous (cf E) := by
  unfold cf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)).abs

omit [CompleteSpace H] in
theorem Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : Fin k → ℂ)
    {x : Fin k → H} (hx : ∀ i, Sm ε σ (x i)) : Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hL] at this
  exact this

theorem key (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∀ p : List (Mx n), (∀ X ∈ p, ∃ i, E i = X) → p.length + l.length ≤ m →
      ‖Dw σ (p ++ l) w‖ ≤ (l.map (cf E)).prod * sobNorm σ (allWords E m) w := by
  induction l with
  | nil =>
    intro p hp hm
    simpa using norm_Dw_le_sobNorm σ ((mem_allWords E m p).2 ⟨by simpa using hm, hp⟩) w
  | cons X l ih =>
    intro p hp hm
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hp' : ∀ Y ∈ p, Y ∈ lieSet ε := fun Y hY => by
      obtain ⟨i, rfl⟩ := hp Y hY
      exact hE i
    have hs := hw.word h.1 hl'
    have e1 : Dw σ (p ++ X :: l) w =
        ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • Dw σ ((p ++ [E i]) ++ l) w := by
      rw [Dw_append]
      show Dw σ p (dRep σ X (Dw σ l w)) = _
      conv_lhs => rw [hx X hX]
      rw [h.dRep_sum hE hs, Dw_sum h.1 hp' _ (fun i => dRep_mem (isUnit_Jm ε) h.1 hs (hE i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dw_append, Dw_append]
      rfl
    rw [e1, List.map_cons, List.prod_cons, mul_assoc, cf, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (ih hl' _ ?_ ?_) (abs_nonneg _)
    · intro Y hY
      rcases List.mem_append.1 hY with hY | hY
      · exact hp Y hY
      · exact ⟨i, (List.mem_singleton.1 hY).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hm ⊢
      omega

theorem sob_le (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (hm : ∀ l ∈ S, l.length ≤ m) :
    sobNorm σ S w ≤ (S.map fun l => (l.map (cf E)).prod).sum * sobNorm σ (allWords E m) w := by
  rw [← List.sum_map_mul_right]
  conv_lhs => unfold sobNorm
  refine List.sum_le_sum fun l hl => ?_
  simpa using key h hE hx m hw l (hS l hl) [] (by simp) (by simpa using hm l hl)

theorem exists_ctrl : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ S₀ : List (List (Mx n)), Words (lieSet ε) S₀ → ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ [] ∈ S ∧ Ctrl (lieSet ε) (UJset ε) σ S ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ w, Sm ε σ w → sobNorm σ S₀ w ≤ A * sobNorm σ S w := by
  intro n ε H _ _ _ σ h S₀ hS₀
  obtain ⟨E, hE, -, hx⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hE' : ∀ i, E i ∈ lieSet ε := fun i => (hE i).1
  have hx' : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i := fun X hX => by
    simpa only [Complex.coe_smul] using hx X hX
  set m := (S₀.map List.length).sum with hm
  have hW : Words (lieSet ε) (allWords E m) := fun l hl X hX => by
    obtain ⟨i, rfl⟩ := ((mem_allWords E m l).1 hl).2 X hX
    exact hE' i
  refine ⟨allWords E m, hW, (mem_allWords E m _).2 (by simp), ?_,
    (S₀.map fun l => (l.map (cf E)).prod).sum, ?_, fun w hw => sob_le h hE' hx' m hw S₀ hS₀ fun l hl => ?_⟩
  · refine ⟨fun g => ((allWords E m).map fun l => (l.map fun X => cf E (Jm ε * gᴴ * Jm ε * X * g)).prod).sum, ?_,
      fun g hg w hw => ?_⟩
    · refine continuous_list_sum _ fun l _ => continuous_list_prod _ fun X _ => ?_
      exact (continuous_cf E).comp (f := fun g : Mx n => Jm ε * gᴴ * Jm ε * X * g)
        (((((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
          continuous_const).matrix_mul continuous_const)).matrix_mul continuous_id)
    · rw [sobNorm_translate h.1 hg hw hW]
      have := sob_le h hE' hx' m hw ((allWords E m).map fun l => l.map fun X => g⁻¹ * X * g) ?_ ?_
      · simpa only [List.map_map, Function.comp_def, inv_eq_UJ hg] using this
      · intro l hl X hX
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact conj_mem_lie (isUnit_Jm ε) hg (hW l' hl' Y hY)
      · intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simpa using ((mem_allWords E m l').1 hl').1
  · refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    refine List.prod_nonneg fun y hy => ?_
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hy
    exact cf_nonneg E X
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

end GlobalTheory.TypeSumCtrl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.ExpansionAverage

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem integrable_K {E : Type} [NormedAddCommGroup E] {F : KG ε → E} (hF : Continuous F) : Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integrable_Dw (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Integrable (fun k : KG ε => e k • Dw σ l (σ (toMK k) w)) (muK ε) :=
  integrable_K (he.smul ((h.continuousOn_Dw hl hw).comp_continuous (continuous_toMK ε) toMK_mem))

theorem Dw_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    Dw σ l (kAvg ε σ e w) = ∫ k, e k • Dw σ l (σ (toMK k) w) ∂(muK ε) := by
  refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
  have h0 : Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) := integrable_Dw h he (l := []) (by simp) hw
  rw [inner_Dw h.1 hl hy hw', kAvg, ← integral_inner h0, ← integral_inner (integrable_Dw h he hl hw),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_Dw h.1 hl hy (hw.translate h.1 (toMK_mem k))]
  ring

theorem form_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ)
    {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    ℓ (kAvg ε σ e w) = ∫ k, e k * ℓ (σ (toMK k) w) ∂(muK ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  have hΛ' : ∀ w, Sm ε σ w → ℓ w = ∑ i, Λ i (Dw σ (S i) w) := hΛ
  rw [hΛ' _ hw']
  simp only [fun i => Dw_kAvg h he (hS i) hw hw',
    fun i => ((Λ i).integral_comp_comm (integrable_Dw h he (hS i) hw)).symm]
  rw [← integral_finsetSum _ fun i _ => (Λ i).integrable_comp (integrable_Dw h he (hS i) hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [hΛ' _ (hw.translate h.1 (toMK_mem k)), Finset.mul_sum, map_smul, smul_eq_mul]

theorem continuousOn_and_hasSum_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (S : List (List (Mx n))) (v : ℕ → H) (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ),
      Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → IsExpn (lieSet ε) (UJset ε) σ S v ℓ C f →
      ContinuousOn f (UJset ε) ∧ ∀ e : KG ε → ℂ, Continuous e → (∀ w, Sm ε σ (kAvg ε σ e w)) → ∀ g ∈ UJset ε,
        HasSum (fun i => ℓ i (σ g (kAvg ε σ e (v i)))) (∫ k, e k * f (g * toMK k) ∂(muK ε)) := by
  intro n ε H _ _ _ σ h S v ℓ C f hS ⟨B, hB, hBd⟩ hE
  have hsc := hE.sobCont hS
  obtain ⟨hv, hC, hb, hsum, hf⟩ := hE
  have hc : ∀ i, ContinuousOn (fun g => ℓ i (σ g (v i))) (UJset ε) := fun i => h.continuousOn_coef (hsc i) (hv i)
  have hbd : ∀ (M : ℝ) i, ∀ g ∈ UJset ε, B g ≤ M → ‖ℓ i (σ g (v i))‖ ≤ M * (C i * sobNorm σ S (v i)) := by
    intro M i g hg hM
    calc ‖ℓ i (σ g (v i))‖ ≤ C i * sobNorm σ S (σ g (v i)) := hb i _ (Sm.translate h.1 (hv i) hg)
      _ ≤ C i * (M * sobNorm σ S (v i)) := mul_le_mul_of_nonneg_left
          ((hBd g hg _ (hv i)).trans (mul_le_mul_of_nonneg_right hM (sobNorm_nonneg _ _ _))) (hC i)
      _ = _ := by ring
  refine ⟨fun g₀ hg₀ => ?_, fun e he hs g hg => ?_⟩
  · have ho : {g | B g < B g₀ + 1} ∈ 𝓝 g₀ := (isOpen_lt hB continuous_const).mem_nhds (lt_add_one (B g₀))
    have h1 : ContinuousOn (fun g => ∑' i, ℓ i (σ g (v i))) (UJset ε ∩ {g | B g < B g₀ + 1}) :=
      continuousOn_tsum (fun i => (hc i).mono Set.inter_subset_left) (hsum.mul_left (B g₀ + 1))
        fun i g hg => hbd _ i g hg.1 (le_of_lt hg.2)
    have h2 : ContinuousOn f (UJset ε ∩ {g | B g < B g₀ + 1}) := h1.congr fun g hg => (hf g hg.1).tsum_eq.symm
    exact (continuousWithinAt_inter ho).1 (h2 g₀ ⟨hg₀, lt_add_one (B g₀)⟩)
  · have hm : ∀ k : KG ε, g * toMK k ∈ UJset ε := fun k => mul_mem_UJ hg (toMK_mem k)
    have hcm : Continuous fun k : KG ε => g * toMK k := continuous_const.mul (continuous_toMK ε)
    obtain ⟨M, hM⟩ := (isCompact_range (hB.comp hcm)).bddAbove
    have hM' : ∀ k : KG ε, B (g * toMK k) ≤ M := fun k => hM ⟨k, rfl⟩
    have hF : ∀ i, Integrable (fun k : KG ε => e k * ℓ i (σ (g * toMK k) (v i))) (muK ε) := fun i =>
      integrable_K (he.mul ((hc i).comp_continuous hcm hm))
    have hS' : Summable fun i => ∫ k, ‖e k * ℓ i (σ (g * toMK k) (v i))‖ ∂(muK ε) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) (fun i => ?_)
        ((hsum.mul_left M).mul_left (∫ k, ‖e k‖ ∂(muK ε)))
      rw [← integral_mul_const]
      refine integral_mono (hF i).norm ((integrable_K he.norm).mul_const _) fun k => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd M i _ (hm k) (hM' k)) (norm_nonneg _)
    have key := hasSum_integral_of_summable_integral_norm hF hS'
    simp only [fun k => ((hf _ (hm k)).mul_left (e k)).tsum_eq] at key
    refine Eq.mpr (congrArg (HasSum · _) (funext fun i => ?_)) key
    have := form_kAvg h he (sobCont_translate h.1 (hsc i) hg) (hv i) (hs (v i))
    simp only [fun k => sigma_mul h.1 hg (toMK_mem k)]
    exact this

end GlobalTheory.ExpansionAverage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftCont

theorem continuous_integral_of_cocompact {G H : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [FirstCountableTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : G → H → ℂ)
    (hK : Continuous fun p : G × H => K p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ g h, K g (γ * h) = K g h) :
    Continuous fun g => ∫ h in 𝓕, K g h ∂μ := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    simpa using hconst.re
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_
  · refine Filter.Eventually.of_forall fun g => ?_
    exact (hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun h => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM (g, c) ⟨hg, hc⟩
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (hK.comp (Continuous.prodMk_left h)).continuousAt

theorem theta_integral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  intro D ψ V W χS χT ω ν 𝓕 s F hω hpos hν h𝓕 hs hF hFinv
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω s hs
  have hK : Continuous fun p : GA D V × GA D W => thetaKO ω p.1 p.2 s * F p.2 :=
    hcont.mul (hF.comp continuous_snd)
  have hKinv : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ g h
    have := hinv 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hFinv γ hγ]
  refine ⟨fun g => ?_, ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      (hK.comp (Continuous.prodMk_right g)) (fun γ hγ h => hKinv γ hγ g h)
  · obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    obtain ⟨_, _, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    exact continuous_integral_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO ω g h s * F h) hK hKinv

end GlobalTheory.DefLiftCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStableStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
end

