import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionSwapLineFamily
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem height_comb_horizontal (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (hY : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] {e : ℕ}
    (hc : CharZero Γ(Z, ⊤)) (he : topologicalKrullDim Z = (e + 1 : ℕ)) {ι : Type} [Fintype ι] (L : ι → HermLB p) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (e + 1)) := by
  have hZ : IsArithVar (i ≫ p) e := hY.of_isClosedImmersion i hc he
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Z (i ≫ p) e hZ).2 ι (fun j => (L j).restr i)).1
  refine ⟨Ψ, fun n g hg => ?_⟩
  have e₁ : ((comb L n).restr i).Isometric (comb (fun j => (L j).restr i) n) := by
    refine HermLB.icls_eq_iff.1 ?_
    rw [HermLB.icls_pull, icls_comb, icls_comb, map_sum]
    simp only [map_zsmul, ← HermLB.icls_pull]
  exact (e₁.isSelfInter hZ (hg.isSelfInter_restrict hY i rfl)).unique hZ (hΨ.1 n)

def moveExp (n : Fin 5 → ℤ) : Fin 5 → ℤ := ![0, 0, n 2, n 3 + n 0, n 4 + n 1]

theorem aeval_lin_moveExp (n : Fin 5 → ℤ) :
    aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) (lin fun j => (n j : ℝ)) =
      lin fun j => (moveExp n j : ℝ) := by
  simp [lin, Fin.sum_univ_five, moveExp, MvPolynomial.algebraMap_eq]
  ring

theorem sum_moveExp {G : Type*} [AddCommGroup G] (x : Fin 5 → G) (h₀ : x 0 = x 3) (h₁ : x 1 = x 4) (n : Fin 5 → ℤ) :
    ∑ j, n j • x j = ∑ j, moveExp n j • x j := by
  simp [Fin.sum_univ_five, moveExp, add_smul, h₀, h₁]
  try abel

theorem fam5_icls_tens (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B)
    (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (A : HermLB q) :
    (fam5 π w H flB fl A 0).icls + (fam5 π w H flB fl A 1).icls =
      (fam5 π w H flB fl A 3).icls + (fam5 π w H flB fl A 4).icls := by
  have a1 := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
  have a2 := VMetric.isometric_det_pull H π w
  have a3 := (GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).pull π w
  have a4 := HermLB.isometric_pull_tens (VMetric.grLB flB 0 H) (VMetric.grLB flB 1 H) π w
  rw [← HermLB.icls_tens, ← HermLB.icls_tens]
  exact HermLB.icls_eq_iff.2 (a1.trans (a2.trans (a3.symm.trans a4)))

theorem mix_general (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {d : ℕ}
    (hp : IsArithVar p (d + 1)) (L : Fin 5 → HermLB p)
    (hdet : (L 0).icls + (L 1).icls = (L 3).icls + (L 4).icls)
    (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (hΦ : IsArFun L (d + 1) Φ)
    (r : ((L 0).dual.tens (L 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((L 0).dual.tens (L 4)).B r)
    (hiso : ∀ z ∈ (((L 0).dual.tens (L 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((L 0).restr i).Isometric ((L 3).restr i))
    (F : MvPolynomial (Fin 5) ℝ) (hF : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0)
    (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ) (hFs : F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1)) :
    Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb L n).archInt ((L 0).dual.tens (L 4)) (d + 1) hr := by
  have := hp.isLocallyNoetherian
  have := hp.isNoetherian

  let Aex : Option (Fin 5) → Fin 5 → ℤ := fun o => o.elim (Pi.single 4 1 - Pi.single 0 1) fun j => Pi.single j 1
  have hΦ' := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L Φ hΦ).2.2 (Option (Fin 5))
    (fun o => o.elim ((L 0).dual.tens (L 4)) L) Aex
    (fun o => by
      cases o with
      | none =>
        refine HermLB.icls_eq_iff.1 ?_
        simp [Aex, icls_comb, HermLB.icls_tens, HermLB.icls_dual, Fin.sum_univ_five, Pi.single_apply]
        done
      | some j => exact isometric_comb_single L j)
  let Φ' := Φ ∘ₗ (aeval fun j => lin fun i => (Aex j i : ℝ) :
    MvPolynomial (Option (Fin 5)) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toLinearMap
  have key (P : MvPolynomial (Fin 5) ℝ) : Φ' (X none * rename some P) = Φ ((X 4 - X 0) * P) := by
    have h1 : (lin fun i => (Aex none i : ℝ)) = X 4 - X 0 := by
      simp [Aex, lin, Fin.sum_univ_five, Pi.single_apply]
      ring
    have h2 : (fun j => lin fun i => (Aex (some j) i : ℝ)) = X := by
      funext j
      simp [Aex, lin, Pi.single_apply]
    simp only [Φ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X, aeval_rename]
    rw [h1]
    congr 2
    exact (congrArg (fun f => aeval f P) h2).trans (aeval_X_left_apply P)

  have hex (n : Fin 5 → ℤ) : ∃ g : Y → ℝ, (comb L n).IsArithHeight g := (hC.arExists k Y p (d + 1) hp).1 (comb L n)
  choose ht hht using hex
  have hmix (n : Fin 5 → ℤ) := (hC.arMix k Y p (d + 1) hp (Fin 5) _ L Φ' hΦ' n (ht n) (hht n) r hr).2
  have hfin : (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ)).Finite :=
    (((L 0).dual.tens (L 4)).div hr).finite_support_mult.subset fun z hz => by simpa using hz

  have hloc (z : Y) : ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ∑ n ∈ s, c n * ht n z = 0 := by
    by_cases hz0 : (((L 0).dual.tens (L 4)).div hr).mult z = 0
    · simp [hz0]
    have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hzs : z ∈ (((L 0).dual.tens (L 4)).div hr).supp := CartierDiv.mem_supp_of_mult_ne_zero hz0
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have e03 : ((L 0).restr i).Isometric ((L 3).restr i) := hiso _ hzs Z i rfl
    have e14 : ((L 1).restr i).icls = ((L 4).restr i).icls := by
      have h₁ := congrArg (HermLB.IsomClass.pull i rfl) hdet
      rw [map_add, map_add, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull,
        HermLB.icls_eq_iff.2 e03] at h₁
      exact add_left_cancel h₁
    have hdim : topologicalKrullDim Z = (d + 1 : ℕ) := GlobalTheory.T.arithmetic_variety_divisor_dimension k Y p (d + 1) hp Z i hz1
    obtain ⟨T, hT⟩ : ∃ T : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ, ∀ (n : Fin 5 → ℤ) (g : Y → ℝ),
        (comb L n).IsArithHeight g → g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (d + 1)) := by
      rcases hp.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arithmetic_height_polynomial_in_degrees k Y p (d + 1) hp Z i ℓ (d + 1) hdim (Fin 5) L
      · have he' : e + 1 = d + 1 := by
          have := he.symm.trans hdim
          exact_mod_cast this
        obtain ⟨T, hT⟩ := height_comb_horizontal hC hp i hc he L
        exact ⟨T, fun n g hg => (hT n g hg).trans (by rw [he'])⟩
    have hmove (n : Fin 5 → ℤ) : ((comb L n).restr i).Isometric ((comb L (moveExp n)).restr i) := by
      refine HermLB.icls_eq_iff.1 ?_
      rw [HermLB.icls_pull, HermLB.icls_pull, icls_comb, icls_comb, map_sum, map_sum]
      simp only [map_zsmul]
      exact sum_moveExp (fun j => HermLB.IsomClass.pull i rfl (L j).icls) (HermLB.icls_eq_iff.2 e03) e14 n
    have hsum : ∑ n ∈ s, c n * ht n (i (genericPoint Z)) = T (aeval (![X 3, X 4, X 2, X 3, X 4] :
        Fin 5 → MvPolynomial (Fin 5) ℝ) F) := by
      rw [hFs, map_sum, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, map_pow, aeval_lin_moveExp, map_smul, smul_eq_mul,
        GlobalTheory.AdjFlag.height_eq hp (hht n) (hht (moveExp n)) i (hmove n), hT _ _ (hht (moveExp n))]
    rw [hsum, hF, map_zero, mul_zero]

  have e₁ : Φ ((X 4 - X 0) * F) = ∑ n ∈ s, c n * Φ' (X none * rename some (lin fun i => (n i : ℝ)) ^ (d + 1)) := by
    rw [hFs, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_pow, key]
  have e₂ : ∑ n ∈ s, c n * ∑ᶠ z, ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z = 0 := by
    have hf (n : Fin 5 → ℤ) :
        (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z).Finite :=
      hfin.subset (Function.support_mul_subset_left _ _)
    simp_rw [mul_finsum]
    rw [← finsum_sum_comm s _ fun n _ => (hf n).subset (Function.support_mul_subset_right _ _)]
    refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
    rw [← hloc z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e₁]
  simp_rw [hmix, mul_sub]
  rw [Finset.sum_sub_distrib, e₂, zero_sub]

theorem mix_dualTaut_tens_quotBase : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y]
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p)
    (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ), IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ)
      (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) →
      ∀ F : MvPolynomial (Fin 5) ℝ, aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0 →
      ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
        Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt
          ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := by
  intro hC k _ B Y _ _ q p d _ hp π w E h H flB fl A Φ hΦ r hr hiso F hF s c hFs
  exact mix_general hC hp (fam5 π w H flB fl A) (fam5_icls_tens k B Y q p π w E h H flB fl A) Φ hΦ r hr hiso F hF s c hFs

end GlobalTheory.CovTest.SwapLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtTopLevel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop

theorem bad_def_lift : Hypotheses2 → GlobalTheory.Published.GreenCuspidal → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  intro hP hGr hG
  have h1 := GlobalTheory.T.finite_group_representation_twist hP hG
  have h2 := GlobalTheory.CovTop.LocShareNum.locShares_le_exp hP hGr
  unfold Lifts at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  obtain ⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩ := a1 i hi
  obtain ⟨ψ₀, hψ₀, hsh⟩ := a2 i
  have hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤
      1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
    intro k
    obtain ⟨X, _, _, _, A, hf, hA, hpm⟩ := hfree k
    obtain ⟨n, hn, hn'⟩ := embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm
    have hle : Pb.comap π ≤ (H k).comap π := fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv
    have h3 := card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb
    refine ⟨n, hn, ?_⟩
    rw [one_mul]
    exact_mod_cast (hn'.trans h3.symm).le
  choose n hn hn' using hc
  obtain ⟨S, hSb, hbd⟩ := GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀
  have hs := hsh S hSb
  unfold BadAt
  rw [hT, hB]
  have hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := Nat.cast_nonneg _
  have hx := Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))
  calc _ ≤ _ := hbd
    _ ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hs hr
    _ ≤ _ := by nlinarith

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FamHom

theorem main : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P)
    (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) →
    CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 →
    ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  intro K _ A A' T P hP β hadd h0
  obtain ⟨M, hM, rfl⟩ := cls_surj β
  have hMa : AbDual.IsAdditive M := (AbDual.isAdditive_iff hM).2 fun Y a a' t => hadd Y a a' t
  obtain ⟨x, hx, hu⟩ := hP.univ T.X M hM hMa
  have hE : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ x)).IsLB := pull_isLB hP.isLB _
  have c : cls M hM = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) := (cls_eq_iff hM hE).2 hx
  have Kx : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (t : Y ⟶ T.X),
      AbDual.evc hP.isLB a (t ≫ x) = AbDual.evc hM a t := by
    intro Y a t
    have k := AbDual.evc_ev hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) hE a t
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k]
    unfold AbDual.evc
    rw [c]
    rfl
  have h1 := (AbDual.triv_ev_iff hM (𝟙 A.X) (1 : A.X ⟶ T.X)).2 h0
  have u : snd A.X (𝟙_ (Over (Sp K))) ≫ (η[T.X] : 𝟙_ (Over (Sp K)) ⟶ T.X) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A.X (𝟙_ (Over (Sp K)))) (toUnit _)]
  have e1 : η[T.X] ≫ x = 1 := by
    apply hP.eq_one
    rw [AbDual.triv_ev_iff hP.isLB, ← Category.assoc, Kx, u, AbDual.evc_one_right hM h1]
  have hpt : η[T.X] ≫ x = η[A'.X] := by
    rw [e1]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit (𝟙_ (Over (Sp K)))) (𝟙 _), Category.id_comp]
  have hmon : IsMonHom x := rigidity_holds (Sp K) T.X A'.X T.ab A'.ab x hpt
  refine ⟨Hom.mk x, c, fun ψ hψ => ?_⟩
  have hE' : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)).IsLB := pull_isLB hP.isLB _
  have hψ' : LBIso M (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)) := (cls_eq_iff hM hE').1 hψ
  exact hom_ext (hu ψ.hom hψ')

end GlobalTheory.AV.FamHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantFirstFacto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic

namespace GlobalTheory.TranslFst

theorem iso_transl_fst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A, (∃ t : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h1 h2 h hh
  have hG : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z : ∀ (f : A ⟶ G2 A), (∃ t : (L.pull f.left).Gen, t.IsGen) → pull f.left (cls L hL) = 0 := by
    intro f hf
    rw [← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_zero_iff _).2 hf
  have fac : ∀ (g : G2 A ⟶ A) (e : A ⟶ G2 A), pull e.left (cls L hL) = 0 → pull (g ≫ e).left (cls L hL) = 0 := by
    intro g e he
    rw [Over.comp_left, pull_comp, he, map_zero]
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hG L hL (G2 A) (lift (fst A A) 1) (toUnit _ ≫ lift h 1)
    (lift 1 (snd A A))
  have e := (cls_linComb hL _ _ (LB.isLB_linComb hL _ _)).symm.trans ((cls_eq_zero_iff _).2 cube)
  have habc : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) * lift 1 (snd A A) =
      GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A) := by
    ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have hac : (lift (fst A A) 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = 𝟙 _ := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hbc : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = snd A A ≫ lift (toUnit A ≫ h) (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hab : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) = (fst A A * (toUnit _ ≫ h)) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have ha : (lift (fst A A) 1 : G2 A ⟶ G2 A) = fst A A ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hb : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hc : (lift 1 (snd A A) : G2 A ⟶ G2 A) = snd A A ≫ lift 1 (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have h1' : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at e
  rw [habc, hac, hbc, hab, ha, hb, hc, h1', Over.id_left, pull_id] at e
  simp only [fun g => fac g _ (z _ h1), fun g => fac g _ (z _ h2), fun g => fac g _ (z _ hh)] at e
  have key : pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left (cls L hL) = cls L hL := by
    simp only [one_smul, neg_smul, smul_zero, neg_zero, add_zero, zero_add] at e
    exact eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans e)
  refine (cls_eq_iff hL (pull_isLB hL _)).1 ?_
  rw [cls_pull hL, key]

end GlobalTheory.TranslFst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantSecondFact
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslInv

theorem translSnd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A,
    (∃ t : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) →
    LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h0 h1 h hh
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA L hL (G2 A) (lift (1 : G2 A ⟶ A) (snd A A))
    (toUnit _ ≫ lift 1 h) (lift (fst A A) 1)
  have zero_of : ∀ {Y : Scheme.{0}} (ψ : Y ⟶ (G2 A).left), (∃ t : (L.pull ψ).Gen, t.IsGen) →
      GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls L hL) = 0 := fun ψ hψ =>
    (GlobalTheory.CechPic.cls_pull hL ψ (pull_isLB hL ψ)).symm.trans ((GlobalTheory.CechPic.cls_eq_zero_iff _).2 hψ)
  have e_abc : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 =
      GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have e_ab : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) =
      (snd A A * (toUnit _ ≫ h)) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_ac : lift (1 : G2 A ⟶ A) (snd A A) * lift (fst A A) 1 = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_bc : (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 = fst A A ≫ lift (𝟙 A) (toUnit A ≫ h) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_a : lift (1 : G2 A ⟶ A) (snd A A) = snd A A ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_b : (toUnit _ ≫ lift 1 h : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_c : lift (fst A A) (1 : G2 A ⟶ A) = fst A A ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_1 : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  obtain ⟨t, ht⟩ := cube
  have hz := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb hL] at hz
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at hz
  rw [e_abc, e_ab, e_ac, e_bc, e_a, e_b, e_c, e_1] at hz
  simp only [Over.comp_left, Over.id_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_id,
    zero_of _ h0, zero_of _ h1, zero_of _ hh, map_zero] at hz
  simp only [one_zsmul, neg_one_zsmul, neg_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hL _)).1
    ((GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)).trans hz).symm

end GlobalTheory.TranslInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEffectiveUpEtaleTowerNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem effAt_etTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  EffAt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  intro K L _ _ cK cL n r R T ι ψ τ x φ θ hT hx hφ hθ hE
  have hinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hT.retr, hT.retr] at this
  have hi : Function.Injective (fun g : R => (ι g : L)) := Subtype.val_injective.comp hinj
  have hι0 : ∀ g : R, g ≠ 0 → (ι g : L) ≠ 0 := fun g hg h =>
    hg (hinj (Subtype.ext (by simpa using h)))
  refine ⟨fun h => ?_, ?_, fun P hP => ?_⟩
  · have hC := GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis cK cL n r R T ι ψ τ x hT hx
    exact one_ne_zero (hC.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  · rw [Finsupp.add_apply]
    have h1 : Finsupp.mapDomain (fun g : R => (ι g : L)) φ 0 = 0 := by
      have e := Finsupp.mapDomain_apply hi φ 0
      simp only [map_zero, ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => hφ 0 h rfl
    have h2 : Finsupp.mapDomain (fun g : T => (g : L)) θ 0 = 0 := by
      have e := Finsupp.mapDomain_apply Subtype.val_injective θ 0
      simp only [ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => (hθ 0 h).1 rfl
    rw [h1, h2, add_zero]
  · have hq : ∀ {M : Type} [Field M] (c : ℂ →+* M) (E : Place c) {A : Type} (f : A → M)
        (ξ : A →₀ ℚ), E.ordQ (Finsupp.mapDomain f ξ) = ξ.sum fun g t => t * (E.ord (f g) : ℚ) := by
      intro M _ c E A f ξ
      rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
      rfl
    have hθ' : 0 ≤ P.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
      rw [hq]
      refine Finset.sum_nonneg fun g hg => mul_nonneg (hθ g hg).2 ?_
      exact_mod_cast (P.ord_nonneg_iff (hθ g hg).1).2 (hP.1 _ g.2)
    rw [hq] at hθ'
    rw [Place.disc, map_add]
    rcases GlobalTheory.T.dvrPlace_centre_on_base_of_etaleTowerOverNormalLocal cK cL r R T ι ψ τ P hT hP with h0 | ⟨P0, hP0, h0⟩
    · rw [GlobalTheory.T.order_differential_form_et_tower cK cL n r R T ι ψ τ x P hT hx hP h0, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) = 0 :=
        Finset.sum_eq_zero fun g hg => by dsimp only; rw [h0 g (hφ g hg)]; simp
      rw [this]
      push_cast
      linarith
    · have h1 := GlobalTheory.T.dvrPlace_ord_eq_along_etaleTower cK cL r R T ι ψ τ P P0 hT hP hP0 h0
      have hd := hE.2.2 P0 hP0
      rw [Place.disc, hq] at hd
      rw [GlobalTheory.T.formOrder_wedge_eq_of_etaleTower_heightOnePrime cK cL n r R T ι ψ τ x P P0 hT hx hP hP0 h1, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) =
          φ.sum fun g t => t * (P0.ord (g : K) : ℚ) :=
        Finset.sum_congr rfl fun g hg => by dsimp only; rw [h1 g (hφ g hg)]
      rw [this]
      linarith

end GlobalTheory.FieldPair
end
end

