import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0541
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) (a : Fin m) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) a.castSucc = (c *ᵥ y) a + u a * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

theorem blk_mulVec_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) (Fin.last m) =
      ∑ j, σ (u j) * y j + d * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

variable [NumberField E]

theorem mem_lastFib_blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y l : Fin m → 𝓞 E) (s : 𝓞 E)
    (h : ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) a + u a * algebraMap (𝓞 E) E s =
      algebraMap (𝓞 E) E (l a)) :
    (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + d * algebraMap (𝓞 E) E s) ∈
      lastFib (blk σ c u d) := by
  have hvI : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (y j))
      (algebraMap (𝓞 E) E s) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨s, by simp⟩
    · exact ⟨y a, by simp⟩
  have h1 := Submodule.mem_sup_right (S := intVec E (m + 1))
    (Submodule.mem_map_of_mem (f := (blk σ c u d).mulVecLin.restrictScalars (𝓞 E)) hvI)
  have h2 : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (l j)) 0 :
      Fin (m + 1) → E) ∈ lam (blk σ c u d) := by
    refine Submodule.mem_sup_left ?_
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨0, by simp⟩
    · exact ⟨l a, by simp⟩
  have h3 := (lam (blk σ c u d)).sub_mem h1 h2
  show LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m) _ ∈ lam (blk σ c u d)
  convert h3 using 1
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [blk_mulVec_last]
  · have hne : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
    simp [blk_mulVec_castSucc, h a, hne]

theorem one_le_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (1 : Submodule (𝓞 E) E) ≤ lastFib C := by
  intro x hx
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_sup_left (show _ ∈ intVec E (m + 1) from ?_)
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    exact ⟨o, by simp⟩
  · exact ⟨0, by simp [hi]⟩

theorem lastFib_fg {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).FG := by
  have hfg : (lam C).FG := (GlobalTheory.T.lam_is_lattice E (m + 1) C).1
  have hmap : ((lastFib C).map
      (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))).FG :=
    Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))
    (fun a b h => by simpa using congrFun h (Fin.last m)) hmap

theorem tor_decomp {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (t : 𝓞 E)
    (ht : t ∈ tor c u) :
    ∃ yo lo : Fin m → 𝓞 E, ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) a +
      u a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (lo a) := by
  have h : t • u ∈ lam c := by
    have h0 := (Ideal.mem_torsionOf_iff _ _).1 ht
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨l, hl, z, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.1 h
  choose lo hlo using hl
  choose yo hyo using hy
  refine ⟨-yo, lo, fun a => ?_⟩
  have h1 := congrFun hz a
  have hy' : (fun j => algebraMap (𝓞 E) E ((-yo) j)) = -y := by
    funext j
    simp [hyo j]
  rw [hy', Matrix.mulVec_neg, hlo a]
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply,
    Algebra.smul_def] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1
end

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  intro F E _ _ _ _ _ σ hCM m c hc u t ht ht0
  obtain ⟨hinv, hfix, hsO, hN⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hCM
  obtain ⟨yo, lo, hyl⟩ := LocalBound.tor_decomp c u t ht
  have hf0 : σ (-∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j)) =
      -∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
    have hs : ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j * σ (algebraMap (𝓞 E) E (yo j)) := by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hc]
      ring
    rw [map_neg, map_sum]
    simp only [map_mul, hinv]
    rw [hs]
  obtain ⟨f, hf⟩ := hfix _ hf0
  refine ⟨f, fun d => ?_⟩
  have hT : tor c u ≠ ⊥ := fun h => ht0 (by simpa [h] using ht)
  have hsOt : sO σ t ≠ 0 := by
    intro h0
    apply ht0
    have h1 : σ (algebraMap (𝓞 E) E t) = 0 := by
      have := hsO t
      rw [h0] at this
      simpa using this.symm
    have h2 : algebraMap (𝓞 E) E t = 0 := by
      rw [← hinv (algebraMap (𝓞 E) E t), h1, map_zero]
    exact (map_eq_zero_iff _ (RingOfIntegers.coe_injective)).1 h2
  have hmem : ∀ t' ∈ tor c u, sO σ t' ∈ (tor c u).map (sO σ) :=
    fun t' h' => Ideal.mem_map_of_mem _ h'
  have h𝔱 : (tor c u).map (sO σ) ≠ ⊥ := by
    intro h0
    have := hmem t ht
    rw [h0] at this
    exact hsOt (by simpa using this)
  have hw := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) yo lo t hyl
  have hinvb : ∀ b : E, (∀ a ∈ (tor c u).map (sO σ), (a : E) * b ∈ (1 : Submodule (𝓞 E) E)) →
      b ∈ lastFib (blk σ c u (algebraMap F E d)) := by
    intro b hb
    obtain ⟨y, hy, hby⟩ := GlobalTheory.T.torsion_orthogonality_integral_solution F E σ hCM m c hc u b (fun t' h' => by
      have := hb _ (hmem t' h')
      rwa [show ((sO σ t' : 𝓞 E) : E) = σ (t' : E) from hsO t'] at this)
    choose lo' hlo' using hy
    have h1 := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) y lo' 0 (fun a => by
      rw [hlo' a]
      simp)
    have h2 := LocalBound.one_le_lastFib (blk σ c u (algebraMap F E d)) hby
    have h3 := Submodule.add_mem _ h1 h2
    have h4 : (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + algebraMap F E d * algebraMap (𝓞 E) E 0) +
        (b - ∑ j, σ (u j) * (y j : E)) = b := by
      simp only [map_zero, mul_zero, add_zero]
      exact add_sub_cancel _ _
    rwa [h4] at h3
  have hnorm := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hCM t).1
  have hkey : ((sO σ t : 𝓞 E) : E) * (∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) +
      algebraMap F E d * algebraMap (𝓞 E) E t) -
      algebraMap F E (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d) ∈ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_one.2 ⟨∑ j, sO σ (lo j) * yo j, ?_⟩
    have hsum : σ (algebraMap (𝓞 E) E t) * ∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) -
          ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hyl j, map_add, map_mul]
      ring
    have hs2 : algebraMap (𝓞 E) E (∑ j, sO σ (lo j) * yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (hsO (lo j))
    rw [hs2, show ((sO σ t : 𝓞 E) : E) = σ (algebraMap (𝓞 E) E t) from hsO t, map_add, map_mul,
      hf, hnorm]
    have hnorm' : (t : E) = algebraMap (𝓞 E) E t := rfl
    rw [hnorm']
    linear_combination -hsum
  have hmain := GlobalTheory.T.denominator_index_bound E ((tor c u).map (sO σ)) h𝔱
    (lastFib (blk σ c u (algebraMap F E d))) (LocalBound.lastFib_fg _)
    (LocalBound.one_le_lastFib _) hinvb (sO σ t) _ _ (hmem t ht) hw hkey
  rw [hN, GlobalTheory.T.denominator_norm_quadratic_extension F E hCM.2.2.1] at hmain
  rw [GlobalTheory.T.delta_block_matrix_multiplicative F E σ m c u (algebraMap F E d)]
  calc delta c * Ideal.absNorm (tor c u) ^ 2 *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2
      = delta c * Ideal.absNorm (tor c u) * (Ideal.absNorm (tor c u) *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimClosureGenericPt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem charZero_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} {e : ℕ} (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := by
  haveI h0 : CharZero Γ(Y, ⊤) := hvar.charZero
  have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
    (Y.residue (genericPoint Y)).hom.injective.comp (germ_injective_of_isIntegral Y _ _)
  haveI h1 : CharZero (Y.residueField (genericPoint Y)) := charZero_of_injective_ringHom hinj
  exact (RingHom.charZero_iff (j.residueFieldMap (genericPoint Y)).hom.injective).2 h1

theorem charZero_image (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [hx : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)] :
    CharZero ((MP ℤ m n).residueField (qpSnd n' m n x)) := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  exact (RingHom.charZero_iff (F.residueFieldMap x).hom.injective).2 hx

theorem dim_closure_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} [IsClosedImmersion j] {e : ℕ}
    (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    topologicalKrullDim (closure ({j (genericPoint Y)} : Set (MP ℤ (m + 1) (consN n' n)))) = ((e + 1 : ℕ) : _) := by
  have hrange : Set.range j = closure {j (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Y).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).trans hvar.dim_eq

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Count

theorem card_mul_measure_le_of_disjoint_translates :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] (L : AddSubgroup G) (S : Set G), MeasurableSet S → S ⊆ L →
    ∀ (ι : Type) [Fintype ι] (f : ι → G), (∀ i, f i ∈ L) →
    (∀ i j u v, u ∈ S → v ∈ S → f i + u = f j + v → i = j) →
    (Fintype.card ι : ℝ≥0∞) * μ S ≤ μ (L : Set G) := by
  intro G _ _ _ μ _ L S hS hSL ι _ f hf hdis
  let T : ι → Set G := fun i => (fun x => -f i + x) ⁻¹' S
  have hT : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_add (-f i)) hS
  have hμ : ∀ i, μ (T i) = μ S := fun i => measure_preimage_add μ (-f i) S
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) T := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    intro x hi hj
    refine hij (hdis i j (-f i + x) (-f j + x) hi hj ?_)
    simp
  have hsub : (⋃ i ∈ (Finset.univ : Finset ι), T i) ⊆ (L : Set G) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    have h1 : -f i + x ∈ L := hSL hi
    have h2 : f i + (-f i + x) ∈ L := L.add_mem (hf i) h1
    simpa using h2
  calc (Fintype.card ι : ℝ≥0∞) * μ S = ∑ i ∈ (Finset.univ : Finset ι), μ (T i) := by
        simp [hμ, Finset.card_univ]
    _ = μ (⋃ i ∈ (Finset.univ : Finset ι), T i) :=
        (measure_biUnion_finset hd (fun i _ => hT i)).symm
    _ ≤ μ (L : Set G) := measure_mono hsub

end GlobalTheory.CompanionTheory.SiegelND.Integ.Count
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIso
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := GlobalTheory.T.double_complex_class_surjective K a j hab
  have hk := GlobalTheory.T.double_complex_lead_zero_of_class_zero K a j hab
  have hi := GlobalTheory.T.double_complex_class_zero_of_lead_zero K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuples
section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN

theorem exists_sdW_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨B, hsym, hdet, -, hR'⟩ :=
    GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (GlobalTheory.CompanionTheory.SW.SdTuples.cf (F := F) (E := E) (AF F) b) := hcc _ b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨μ, hμ⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym' hdet'
    (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M)
  refine ⟨μ, ?_⟩
  unfold SdW
  have hf : (fun X Y : Fin n → Fin M → AF F ⊗[F] E => ψ (BR (AF F) σ J X Y)) = fun X Y =>
      ψ (dotProduct (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M X) (Matrix.mulVec
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F (AF F)))
        (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M Y))) := by
    funext X Y
    rw [← GlobalTheory.CompanionTheory.SW.SdTuples.BR_eq hc J B (hR' (AF F)).1 X Y]
  rw [hf]
  exact hμ

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound

theorem twisted_integral_finite_coset_combination_bound :
    ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  intro X _ _ _ _ _ _ _ m _ L hc ho q hq hn K hK Q s hQ
  have hopen : ∀ a : X, IsOpen {y : X | y - a ∈ L} := fun a =>
    ho.preimage (continuous_id.sub continuous_const)
  have hmeas : ∀ a : X, MeasurableSet {y : X | y - a ∈ L} := fun a => (hopen a).measurableSet
  have hcomp : ∀ a : X, IsCompact {y : X | y - a ∈ L} := by
    intro a
    have himg : {y : X | y - a ∈ L} = (fun x => x + a) '' (L : Set X) := by
      ext y
      constructor
      · intro hy
        exact ⟨y - a, hy, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [himg]
    exact hc.image (continuous_id.add continuous_const)
  have hion : ∀ a : X, IntegrableOn q {y : X | y - a ∈ L} m := fun a =>
    hq.continuousOn.integrableOn_compact (hcomp a)
  have hterm : ∀ a : X, (fun x => Set.indicator {y : X | y - a ∈ L} (fun _ => (1 : ℂ)) x * q x)
      = Set.indicator {y : X | y - a ∈ L} q := by
    intro a
    funext x
    by_cases hx : x ∈ {y : X | y - a ∈ L}
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∀ a : X, Integrable (Set.indicator {y : X | y - a ∈ L} q) m := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hion a)
  have hfun : (fun x => Q x * q x)
      = fun x => ∑ a ∈ s, Q a * Set.indicator {y : X | y - a ∈ L} q x := by
    funext x
    conv_lhs => rw [hQ x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, congrFun (hterm a) x]
  have hsum : ∫ x, Q x * q x ∂m = ∑ a ∈ s, Q a * ∫ x in {y : X | y - a ∈ L}, q x ∂m := by
    rw [hfun, integral_finsetSum s (fun a _ => (hint a).const_mul (Q a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_indicator (hmeas a)]
  have hone : ∀ a : X, ‖∫ x in {y : X | y - a ∈ L}, q x ∂m‖ ≤ √K := by
    intro a
    have h := Real.abs_le_sqrt (hK a)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hone a) (norm_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponentStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_spectral_of_strict_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | exact GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | (intros; apply GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict <;> assumption)
end

