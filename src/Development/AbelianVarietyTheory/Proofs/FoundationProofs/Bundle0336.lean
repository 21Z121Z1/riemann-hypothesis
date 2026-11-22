import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0334

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZeroStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  first | exact @GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | exact GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | (intros; apply GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLengthStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  first | exact @GlobalTheory.InertLatLength.absEv_det_eq_of_inert | exact GlobalTheory.InertLatLength.absEv_det_eq_of_inert | (intros; apply GlobalTheory.InertLatLength.absEv_det_eq_of_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersectionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∀ d : Fin n → (Fv F v)ˣ, IsElemDiv (splitEquivIn h hJ τ β g) d → absEv F E v (Matrix.GeneralLinearGroup.det α) = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹ := by
  first | exact @GlobalTheory.SplitInterDet.absEv_det_split | exact GlobalTheory.SplitInterDet.absEv_det_split | (intros; apply GlobalTheory.SplitInterDet.absEv_det_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdeleCoverModFieldShrunkCompactStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (Ω : Set (AF F)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C * ((2 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω := by
  first | exact @GlobalTheory.Eis.ConvCover.exists_cover | exact GlobalTheory.Eis.ConvCover.exists_cover | (intros; apply GlobalTheory.Eis.ConvCover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmAdeleSplitComplexFiniteAdelesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmAdele_split_complex_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : (AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E, Continuous e.symm ∧ (∀ x : E, e (inclR (F := F) (AF F) x) = (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧ e (halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  first | exact @GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | exact GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | (intros; apply GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
section
noncomputable section

open Formalism.UG Formalism.IndefR.Mult GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.UnitaryDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem exists_cartan (hU : IsUnramInv ϖ σ q) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin n) (intL L), ∃ k₂ ∈ GLint (Fin n) (intL L),
      (g : Matrix (Fin n) (Fin n) L) = (k₁ : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin n) (Fin n) L) := by
  have hnt := P.fSatake_nontriv hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  obtain ⟨c, hc0, hg, -⟩ := P.glint_exists_denom (n := Fin n) A g
  refine P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ (unif_ne_zero hU) (fun x hx => ?_) g c hc0 hg
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [hϖ, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log hx']

theorem good_of_mem (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a)
    {g : GL (Fin n) L} (hg : g ∈ GU σ n) {k₁ k₂ : GL (Fin n) L} (h₁ : k₁ ∈ GLint (Fin n) (intL L))
    (h₂ : k₂ ∈ GLint (Fin n) (intL L))
    (e : g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) : Good n d := by
  have hπ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 hg
    ⟨ϖ, hπ, k₁, h₁, k₂, h₂, e⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  rw [e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL L)) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem h₁) ha)) (ent (mul_mem hb (inv_mem h₂))) ?_ k
    calc _ = (k₁⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem ha) h₁)) (ent (mul_mem h₂ (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

theorem exists_good_div : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧
      ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L),
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  intro L _ _ ϖ σ q n hU g
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ := exists_cartan hU (g : GL (Fin n) L)
  have hd : ∀ i : Fin n, (List.ofFn a).getD i.1 0 = a i := fun i => by simp [List.getD_eq_getElem?_getD]
  have e' : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ (List.ofFn a).getD i.1 0) * k₂.1 := by
    simp only [hd]; exact e
  exact ⟨List.ofFn a, good_of_mem hU List.length_ofFn
    (List.pairwise_ofFn.2 fun i j hij => ha hij.le) g.2 h₁ h₂ e', k₁, h₁, k₂, h₂, e'⟩

end GlobalTheory.LFun.UnitaryDiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem hecke_induction {p : (G → ℂ) → Prop} (h0 : p 0)
    (hadd : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, p f → p f' → p (f + f'))
    (hind : ∀ (r : ℂ) (g : G), p (r • dosetInd ℂ K g)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : p f := by
  classical
  obtain ⟨e, he⟩ := Final.HeckeBasis G K ℂ
  suffices ∀ a, p (e.symm a) by simpa using this (e ⟨f, hf⟩)
  intro a
  induction a using Finsupp.induction_linear with
  | zero => simpa using h0
  | add a b ha hb => rw [map_add]; exact hadd _ (e.symm a).2 _ (e.symm b).2 ha hb
  | single c r =>
    obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk K K g = c := Quotient.exists_rep c
    convert hind r g
    funext x
    rw [← he, e.apply_symm_apply, Finsupp.single_apply, Pi.smul_apply, dosetInd, Set.indicator_apply]
    have : DoubleCoset.mk K K g = DoubleCoset.mk K K x ↔ x ∈ DoubleCoset.doubleCoset g (K : Set G) K := by
      rw [DoubleCoset.eq, DoubleCoset.mem_doubleCoset]; rfl
    by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]

theorem heckeVec_add (hK : IsCommensurated K) (ρ : Representation ℂ G V) {f f' : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (hf' : f' ∈ Hecke ℂ K) (x : V) : heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  simp only [heckeVec, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)

theorem heckeVec_smul (hK : IsCommensurated K) (ρ : Representation ℂ G V) (r : ℂ) {f : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (x : V) : heckeVec ρ K (r • f) x = r • heckeVec ρ K f x := by
  simp only [heckeVec, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (smul_finsum' r (finite_heckeVec hK hf ρ x)).symm

theorem dosetInd_comp (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') (t : H) :
    dosetInd ℂ K' t ∘ e = dosetInd ℂ K (e.symm t) := by
  funext g
  have : e g ∈ DoubleCoset.doubleCoset t (K' : Set H) K' ↔ g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨e.symm a, (hK _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), e.injective (by simpa using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨e a, (hK _).1 ha, e b, (hK _).1 hb, by simp⟩
  by_cases hg : g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K
  · simp [dosetInd, hg, this.2 hg]
  · simp [dosetInd, hg, mt this.1 hg]

theorem dosetInd_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) (t : G) : dosetInd ℂ K (a * t * b) = dosetInd ℂ K t := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, rfl⟩)]

end Generic

section Unitary

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  {σ : w.adicCompletion E →+* w.adicCompletion E} {n q : ℕ} {ϖ : w.adicCompletion E}
  {V : Type} [AddCommGroup V] [Module ℂ V]

open GlobalTheory.InertThetaCompare in

theorem cartanU (hU : IsUnramInv ϖ σ q) (g : GU σ n) : ∃ (d : Fin n → ℤ) (t : GU σ n), Antitone d ∧
    t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  have hϖ : IsUnifV E w ϖ := hU.2.2.2.1
  obtain ⟨d, hd, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp E w n ϖ (mem_Ov_of_isUnifV hϖ) hϖ g.1
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  have hh' : h ∈ GLint (Fin n) (Ov E w) := hh
  have hd' : ∀ i : Fin n, (List.ofFn d).getD i.1 0 = d i := fun i => by simp [List.getD_eq_getElem?_getD]
  have hG : Good n (List.ofFn d) := good_of_unitary hU (π := ϖ) hϖ (by simp)
    (List.pairwise_ofFn.2 fun i j hij => hd hij.le)
    (GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eh) g.2)
    ⟨h * k₁, mul_mem hh' h₁, k₂ * h⁻¹, mul_mem h₂ (inv_mem hh'), by
      simp only [Units.val_mul, e, hd', inv_inv, Matrix.mul_assoc]; rfl⟩
  obtain ⟨t, ht⟩ := exists_diag hU hG
  simp only [hd'] at ht
  exact ⟨d, t, hd, ht, dc_GU hU (a := k₁) (b := k₂) h₁ h₂ (Units.ext (by simp only [Units.val_mul, ht]; exact e))⟩

theorem isSatVecU_of_diag (hU : IsUnramInv ϖ σ q) {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (h0 : x ≠ 0) (hx : x ∈ fixed ρ (KU σ n))
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      heckeVec ρ (KU σ n) (dosetInd ℂ (KU σ n) t) x = SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) • x) :
    IsSatVecU ϖ q ρ x α := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hm := Final.DosetIndMem _ (KU σ n) ℂ
  refine ⟨h0, hx, fun f hf => ?_⟩
  refine hecke_induction (K := KU σ n)
    (p := fun f => heckeVec ρ (KU σ n) f x = SatU ϖ q f (fun i => (α i : ℂ)) • x) ?_ ?_ ?_ hf
  · simp [heckeVec, SatU]
  · intro f hf f' hf' h1 h2
    have := hy.2.2 _ (add_mem hf hf')
    rw [heckeVec_add hK _ hf hf', hy.2.2 _ hf, hy.2.2 _ hf', ← add_smul] at this
    rw [heckeVec_add hK _ hf hf', h1, h2, ← add_smul, smul_left_injective ℂ hy.1 this]
  · intro r g
    obtain ⟨d, t, hd, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
    rw [dosetInd_mul h₁ h₂]
    have := hy.2.2 _ (Submodule.smul_mem _ r (hm t))
    rw [heckeVec_smul hK _ r (hm t), hy.2.2 _ (hm t), smul_smul] at this
    rw [heckeVec_smul hK _ r (hm t), h d t hd ht, smul_smul, smul_left_injective ℂ hy.1 this]

end Unitary

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsEigenSys (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (c : List ℤ → ℂ) : Prop :=
  ∀ (a : GL (Fin n) (w.adicCompletion E)) (g : GLoc σ J v) (d : Fin n → ℤ) (u : Fin n → w.adicCompletion E),
    IsFrameAt w L a → Antitone d → (∀ i, Valued.v (u i) = WithZero.exp (-d i)) →
    (a⁻¹ * locMat σ J h g * a).1 = Matrix.diagonal u →
    heckeVec ρ (stabLoc σ J L v) (dosetInd ℂ (stabLoc σ J L v) g) x = c (List.ofFn d) • x

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {c : List ℤ → ℂ}
  {B : Multiset ℂˣ}

theorem IsEigenSys.split (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x =
      c (List.replicate j 1 ++ List.replicate (n - j) 0) • x := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let t : GL (Fin n) (w.adicCompletion E) := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (by
    rw [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0])
  have ht : Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (KGL w n) t := by
    rw [Tj, dosetInd]
    congr 1
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, Units.ext e⟩,
      fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, congrArg Units.val e⟩⟩
  obtain ⟨⟨a, ha, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Tj_mem_hecke hϖ j).1 hx, ht, dosetInd_comp e e2,
    hc a (e.symm t) (fun i => if i.1 < j then 1 else 0) (fun i => if i.1 < j then ϖ else 1) ha
      (fun i k hik => ?_) (fun i => ?_) (by rw [← e1, e.apply_symm_apply]; rfl)]
  · congr 2
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    by_cases hi : i < j <;> simp [hi, List.getElem_append]
  · have : i.1 ≤ k.1 := hik
    dsimp only
    split_ifs <;> omega
  · split_ifs
    · exact hϖ
    · simp

theorem IsEigenSys.inert (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {τ : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU τ n} (he : IsInertChart σ J L h τ e)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {d : Fin n → ℤ} {t : GU τ n} (hd : Antitone d)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KU τ n) (dosetInd ℂ (KU τ n) t) x = c (List.ofFn d) • x := by
  obtain ⟨-, ⟨a, ha, -, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Final.DosetIndMem _ _ ℂ t).1 hx, dosetInd_comp e e2,
    hc a (e.symm t) d _ ha hd (fun i => ?_) (by rw [← e1, e.apply_symm_apply, ht])]
  rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
  simp

theorem IsEigenSys.isSysParam (hc : IsEigenSys σ J L h ρ x c) (hB : IsParamVec σ J L h ρ x B) :
    IsSysParam σ n h c B := by
  have hx := hB.mem_fixed
  rcases hB with ⟨hv, e, he, hB⟩ | ⟨hw, τ, ϖ, e, α, hU, he, hB, rfl⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    exact Or.inl ⟨hv, hB.2.2.1, fun j hj =>
      smul_left_injective ℂ hB.1 ((hc.split hx he hϖ hj).symm.trans (hB.2.2.2 ϖ hϖ j hj))⟩
  · exact Or.inr ⟨hw, τ, ϖ, α, hU, he.1, rfl, fun d t hd ht => smul_left_injective ℂ hB.1
      ((hc.inert hx he hU.2.2.2.1 hd ht).symm.trans (hB.2.2 _ (Final.DosetIndMem _ _ ℂ t)))⟩

theorem IsEigenSys.isParamVec (hc : IsEigenSys σ J L h ρ x c) (h0 : x ≠ 0) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    (hs : IsSplit (E := E) v → ∃ e, IsSplitChart σ J L h e)
    (hi : IsInertAt F E v w → ∀ τ, IsConjAt σ h τ → ∃ e, IsInertChart σ J L h τ e)
    (hB : IsSysParam σ n h c B) : IsParamVec σ J L h ρ x B := by
  rcases hB with ⟨hv, h1, h2⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, h2⟩
  · obtain ⟨e, he⟩ := hs hv
    exact Or.inl ⟨hv, e, he, h0, (mem_fixed_comp_symm e he.2).2 hx, h1, fun ϖ hϖ j hj => by
      rw [hc.split hx he hϖ hj, h2 j hj]⟩
  · obtain ⟨e, he⟩ := hi hw τ hτ
    exact Or.inr ⟨hw, τ, ϖ, e, α, hU, he, isSatVecU_of_diag hU h0 ((mem_fixed_comp_symm e he.2.2).2 hx)
      fun d t hd ht => by rw [hc.inert hx he hU.2.2.2.1 hd ht, h2 d t hd ht], rfl⟩

end Place

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_isEig_const | exact GlobalTheory.PsType.eq_zero_of_isEig_const | (intros; apply GlobalTheory.PsType.eq_zero_of_isEig_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs
  have hnear := GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  refine ⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1,
    GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCoverStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  first | exact @GlobalTheory.Eis.Conv.CovSkew.cover_skew | exact GlobalTheory.Eis.Conv.CovSkew.cover_skew | (intros; apply GlobalTheory.Eis.Conv.CovSkew.cover_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinityStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  first | exact @GlobalTheory.Eis.Conv.absE_halfE | exact GlobalTheory.Eis.Conv.absE_halfE | (intros; apply GlobalTheory.Eis.Conv.absE_halfE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomial
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}

open Classical in

def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
end

