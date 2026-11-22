import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitarStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  first | exact @GlobalTheory.SuppLocal.supp_local | exact GlobalTheory.SuppLocal.supp_local | (intros; apply GlobalTheory.SuppLocal.supp_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
section
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace GlobalTheory.Hk3.MinuscTopLocal

theorem ov_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.UG.Ov F v = Formalism.UG.intL (v.adicCompletion F) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).trans Iff.rfl

theorem zpow_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) (m : ℤ) :
    ϖ ^ m ∈ Formalism.UG.intL (v.adicCompletion F) ↔ 0 ≤ m := by
  rw [← ov_eq]
  show ϖ ^ m ∈ v.adicCompletionIntegers F ↔ 0 ≤ m
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

def dU {L : Type} [Field L] {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (e : Fin n → ℤ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ e i
  inv := Matrix.diagonal fun i => ϖ ^ (-e i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp

theorem intM_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA _ _) (hB _ _)

theorem intM_diag {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {e : Fin n → ℤ} (he : ∀ i, 0 ≤ e i) :
    ∀ i j, (Matrix.diagonal fun i => ϖ ^ e i) i j ∈ Formalism.UG.intL (v.adicCompletion F) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact (zpow_int hϖ _).2 (he i)
  · exact zero_mem _

theorem unif_ne_zero {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem cartan_top_step : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  intro F _ _ v n ϖ hϖ d k hd hd0 hk a₁ ha₁ a₂ ha₂ a₃ ha₃ d' hd' k₁ hk₁ k₂ hk₂ e
  have h0 : ϖ ≠ 0 := unif_ne_zero hϖ
  rw [ov_eq] at ha₁ ha₂ ha₃ hk₁ hk₂
  have hm0 : ∀ i, 0 ≤ (fun i => if 0 < d i then d i - 1 else d i) i := fun i => by
    have := hd0 i; dsimp only; split_ifs <;> omega
  have hw0 : ∀ i : Fin n, 0 ≤ (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) i := fun i => by
    dsimp only; split_ifs <;> omega
  have hG : a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃ = k₁ * dU h0 d' * k₂ :=
    Units.ext (by simp only [Units.val_mul]; exact e)
  have hD : k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ = dU h0 d' := by
    rw [hG]; group
  have hd'0 : ∀ i, 0 ≤ d' i := by
    intro i
    have hI : ∀ a b, ((k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) _) a b ∈ Formalism.UG.intL (v.adicCompletion F) := by
      simp only [Units.val_mul]
      refine intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₁)) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₂))
      refine intM_mul (intM_mul (intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry ha₁) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry ha₂)) ?_) (GlobalTheory.Hk3.MinuscTop.glint_entry ha₃)
      · exact intM_diag hϖ hm0
      · exact intM_diag hϖ hw0
    have := hI i i
    rw [hD] at this
    change (Matrix.diagonal fun i => ϖ ^ d' i) i i ∈ _ at this
    rw [Matrix.diagonal_apply_eq] at this
    exact (zpow_int hϖ _).1 this
  obtain ⟨dN, hdN⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d i :=
    ⟨fun i => (d i).toNat, fun i => Int.toNat_of_nonneg (hd0 i)⟩
  obtain ⟨d'N, hd'N⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d' i :=
    ⟨fun i => (d' i).toNat, fun i => Int.toNat_of_nonneg (hd'0 i)⟩
  have hdA : Antitone dN := fun i j h => by have := hd h; have := hdN i; have := hdN j; omega
  have hd'A : Antitone d'N := fun i j h => by have := hd' h; have := hd'N i; have := hd'N j; omega
  have hkN : ∀ i : Fin n, 0 < dN i ↔ (i : ℕ) < k := fun i => by rw [← hk i, ← hdN i]; omega
  have hg : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ (dN i - 1) := by
    refine ⟨a₁⁻¹, inv_mem ha₁, a₂⁻¹, inv_mem ha₂, ?_⟩
    have : a₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * a₂⁻¹ =
        dU h0 (fun i => if 0 < d i then d i - 1 else d i) := by group
    rw [this]
    change (Matrix.diagonal fun i => ϖ ^ (if 0 < d i then d i - 1 else d i)) = _
    congr 1; funext i
    rw [← zpow_natCast]; congr 1
    have := hdN i
    split_ifs <;> omega
  have ha : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1 := by
    refine ⟨1, one_mem _, a₃⁻¹, inv_mem ha₃, ?_⟩
    have : 1 * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * a₃⁻¹ =
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) := by group
    rw [this]
    change (Matrix.diagonal fun i : Fin n => ϖ ^ (if (i : ℕ) < k then (1 : ℤ) else 0)) = _
    congr 1; funext i
    split_ifs <;> simp
  have hga : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * ((a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) *
        (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃)) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ d'N i := by
    refine ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, ?_⟩
    rw [← mul_assoc (a₁ * _ * a₂), hD]
    change (Matrix.diagonal fun i => ϖ ^ d' i) = _
    congr 1; funext i
    rw [← hd'N i, zpow_natCast]
  have key := GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule (v.adicCompletion F) ϖ n hϖ dN k hdA hkN _ _ hg ha
    d'N hd'A hga
  refine ⟨hd'0, ?_⟩
  have s1 : ∑ i, d' i = ((∑ i, d'N i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hd'N i).symm
  have s2 : ∑ i, d i = ((∑ i, dN i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hdN i).symm
  have s3 : ∑ i, d' i ^ 2 = ((∑ i, d'N i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hd'N i]
  have s4 : ∑ i, d i ^ 2 = ((∑ i, dN i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hdN i]
  rcases key with h | ⟨h1, h2⟩
  · left; funext i; rw [← hd'N i, ← hdN i, h]
  · right
    rw [s1, s2, s3, s4]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end GlobalTheory.Hk3.MinuscTopLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem residue_map_equiv {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R ≃+* R') {a b : R} (h : IsLocalRing.residue R a = IsLocalRing.residue R b) :
    IsLocalRing.residue R' (φ a) = IsLocalRing.residue R' (φ b) := by
  have h' : IsLocalRing.residue R (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h') ((isUnit_map_iff φ _).1 hu)

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (Formalism.AUTREP.GAf L n)) (Dset : Set (Formalism.AUTREP.GAf L n))
    (hfin : ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Dset).Finite)
    (c : ℂ) (f f' : Formalism.AUTREP.GAf L n → W) :
    Formalism.L2.NG.heckeD J Dset (c • f + f') = c • Formalism.L2.NG.heckeD J Dset f + Formalism.L2.NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : Formalism.AUTREP.GAf L n → W,
      Function.support (fun cc : Formalism.AUTREP.GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : Formalism.AUTREP.GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (Formalism.AUTREP.GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply, Pi.smul_apply]
  simp only [Formalism.L2.NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem cls_eq_of_residue : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : Algebra.adjoin O S →ₐ[O] O), (∀ a (h : a ∈ S), IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin h⟩) = IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin h⟩)) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  first
  | exact @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | (apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators ..)

theorem pt_of_eigvec : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Set (Module.End K V)) (e : V), e ≠ 0 → Function.Injective (algebraMap O K) → (∀ a ∈ S, ∃ c : O, a e = algebraMap O K c • e) → ∃ ψ : Algebra.adjoin O S →ₐ[O] O, (∀ t : Algebra.adjoin O S, (t : Module.End K V) e = algebraMap O K (ψ t) • e) ∧ e ∈ Formalism.L2.NCov.W (Algebra.adjoin O S) (Formalism.L2.NCov.pt ψ) := by
  intro O K V _ _ _ _ _ _ _ S e he hinj hS
  have key : ∀ t ∈ Algebra.adjoin O S, ∃ c : O, t e = algebraMap O K c • e := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha => exact hS a ha
    | algebraMap r => exact ⟨r, by rw [Formalism.L2.NCov.algebraMap_end_eq]; simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 + c2, by rw [LinearMap.add_apply, h1, h2, map_add, add_smul]⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 * c2, by rw [Module.End.mul_apply, h2, map_smul, h1, smul_smul, map_mul, mul_comm]⟩
  choose f hf using fun t : Algebra.adjoin O S => key t t.2
  have uniq : ∀ c c' : O, algebraMap O K c • e = algebraMap O K c' • e → c = c' :=
    fun c c' hcc => hinj (smul_left_injective K he hcc)
  have f1 : f 1 = 1 := uniq _ _ (by rw [← hf 1, map_one, one_smul]; rfl)
  have fm : ∀ s t, f (s * t) = f s * f t := fun s t => uniq _ _ (by
    rw [← hf (s * t), map_mul, mul_comm, mul_smul, ← hf s, ← map_smul, ← hf t]; rfl)
  have f0 : f 0 = 0 := uniq _ _ (by rw [← hf 0, map_zero, zero_smul]; rfl)
  have fa : ∀ s t, f (s + t) = f s + f t := fun s t => uniq _ _ (by
    rw [← hf (s + t), map_add, add_smul, ← hf s, ← hf t]; rfl)
  have fc : ∀ r, f (algebraMap O (Algebra.adjoin O S) r) = r := fun r => uniq _ _ (by
    rw [← hf]
    show (algebraMap O (Module.End K V) r) e = _
    rw [Formalism.L2.NCov.algebraMap_end_eq]; simp)
  let ψ : Algebra.adjoin O S →ₐ[O] O :=
    { toFun := f, map_one' := f1, map_mul' := fm, map_zero' := f0, map_add' := fa, commutes' := fc }
  refine ⟨ψ, fun t => hf t, ?_⟩
  refine (Submodule.mem_iInf _).2 fun t => ?_
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.L2.NCov.pt]
  rw [hf t]
  exact sub_self _

theorem descent : ∀ {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type} (Mg : G → Matrix ι ι K) (d : ι → C), d ≠ 0 → (∀ g, Matrix.mulVec ((Mg g).map φ) d = 0) → ∃ c : ι → K, c ≠ 0 ∧ ∀ g, Matrix.mulVec (Mg g) c = 0 := by
  intro K C _ _ φ ι _ G Mg d hd hdg
  classical
  by_contra hne
  push_neg at hne
  let kerS : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kerS s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kerS s) ≤ Module.finrank K (kerS s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hbot : kerS s = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    by_contra hc0
    obtain ⟨g, hg⟩ := hne c hc0
    have hins : kerS (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kerS s := by
      simp only [kerS, Finset.iInf_insert]
    have hle : kerS (insert g s) ≤ kerS s := by rw [hins]; exact inf_le_right
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
    have hc' : c ∈ kerS (insert g s) := heq ▸ hc
    rw [hins] at hc'
    exact hg (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hc').1)
  let R : Matrix (↥s × ι) ι K := fun p b => Mg p.1.1 p.2 b
  have hinjR : Function.Injective (Matrix.toLin' R) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [← hbot]
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    funext a
    have hc' : Matrix.mulVec R c = 0 := by rw [← Matrix.toLin'_apply]; exact LinearMap.mem_ker.1 hc
    have := congrFun hc' (⟨g, hg⟩, a)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, R] using this
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' R) (LinearMap.ker_eq_bot.2 hinjR)
  have hLR : LinearMap.toMatrix' Ψ * R = 1 := by
    have := congrArg LinearMap.toMatrix' hΨ
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hLRC : (LinearMap.toMatrix' Ψ).map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, hLR, Matrix.map_one φ φ.map_zero φ.map_one]
  have hRd : Matrix.mulVec (R.map φ) d = 0 := by
    funext p
    have := congrFun (hdg p.1.1) p.2
    simp only [Matrix.mulVec, dotProduct] at this
    exact this
  apply hd
  calc d = Matrix.mulVec ((LinearMap.toMatrix' Ψ).map φ * R.map φ) d := by rw [hLRC, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRd, Matrix.mulVec_zero]

theorem coeff_monic_poly_sum {R : Type} [Semiring R] (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (c : ℕ → R) :
    (X ^ n + ∑ k' ∈ Finset.Icc 1 n, C (c k') * X ^ (n - k')).coeff (n - k) = c k := by
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [coeff_C_mul_X_pow, if_neg]
    rw [Finset.mem_Icc] at hb
    omega
  · intro hk
    exact absurd (Finset.mem_Icc.2 ⟨hk1, hk2⟩) hk

theorem coeff_extract : ∀ {O : Type} [CommRing O] [IsLocalRing O] (ι : O →+* ℂ), Function.Injective ι → ∀ (n q : ℕ), IsUnit (q : O) → ∀ (p : O[X]) (lam : ℕ → ℂ) (t : ℕ → O), p.map ι = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (n - k) → p.map (IsLocalRing.residue O) = (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) * t k) * X ^ (n - k)).map (IsLocalRing.residue O) → ∀ k, 1 ≤ k → k ≤ n → ∃ a : O, ι a = lam k ∧ IsLocalRing.residue O a = IsLocalRing.residue O (t k) := by
  intro O _ _ ι hι n q hq p lam t h1 h2 k hk1 hk2
  set u : O := (-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) with hu_def
  have hu : IsUnit u := ((isUnit_one.neg).pow k).mul (hq.pow _)
  have e1 : ι (p.coeff (n - k)) = ι u * lam k := by
    have := congrArg (fun P : ℂ[X] => P.coeff (n - k)) h1
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1) ^ k' * (q : ℂ) ^ (k' * (k' - 1) / 2) * lam k')]
    simp [u]
  have e2 : IsLocalRing.residue O (p.coeff (n - k)) = IsLocalRing.residue O (u * t k) := by
    have := congrArg (fun P : (IsLocalRing.ResidueField O)[X] => P.coeff (n - k)) h2
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1 : O) ^ k' * (q : O) ^ (k' * (k' - 1) / 2) * t k')]
  refine ⟨↑hu.unit⁻¹ * p.coeff (n - k), ?_, ?_⟩
  · rw [map_mul, e1, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
  · rw [map_mul, e2, ← map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]

theorem normV_unit : ∀ (D : D7) (i : D.nd.Loc) (w : PlE D.host), w ∉ placesOver D.host.E (D.nd.l i) → IsUnit (((normV w : ℕ) : D.nd.O i)) := by
  intro D i w hw
  classical
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hN : ¬ (D.nd.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : D.nd.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := hu.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  rwa [map_natCast] at this

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  first | exact @GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | exact GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | (intros; apply GlobalTheory.TwEig.pairComm_eigSum_sub_iSup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DepthZeroJacquetInjectiveOfAdmissible
section
namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  first | exact @GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | exact GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | (intros; apply GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigSumMulProjEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

open Formalism.L2.Col in

theorem eigSum_mul_proj_eq {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hr : (⨆ c, Ec c) = LinearMap.range e)
    (hh : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    PairComm (fun i => h i * e) ∧ ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
      eigSum (fun i => h i * e) Q = ⨆ (c : C) (_ : Q (lab c)), Ec c := by
  first
  | exact @_root_.GlobalTheory.IndependentInfimum.main
  | exact _root_.GlobalTheory.IndependentInfimum.main
  | (apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndependentInfimum.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndependentInfimum.main ..)

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  first | exact @GlobalTheory.HkUp.eigen_up_along_adjoint | exact GlobalTheory.HkUp.eigen_up_along_adjoint | (intros; apply GlobalTheory.HkUp.eigen_up_along_adjoint <;> assumption)
end

