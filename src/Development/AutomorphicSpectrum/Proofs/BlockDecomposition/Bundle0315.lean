import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftClosedEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompatibleFamilyOfSingleton
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_compatible_family_of_singleton : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) := by
  intro ι _ _ A _ P _ _ res hid hcomp hker hext i f
  have inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h) := by
    rintro S _ h rfl a b hab
    rwa [hid, hid] at hab
  set x : MvPolynomial ι A := MvPolynomial.X i with hx

  have h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}),
      res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f := by
    intro j
    obtain ⟨k, g, hg⟩ := hext {j} i (res {i} {i, j} (sub_pair_left i j) f)
      (Finset.singleton_nonempty j)
    exact ⟨k, g, hg⟩
  choose k g hg using h1
  set K : ℕ := Finset.univ.sup k with hK
  have hkK : ∀ j, k j ≤ K := fun j => Finset.le_sup (Finset.mem_univ j)
  obtain ⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j)
      = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by
    refine ⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩
    simp only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]

  have htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T),
      res {j} T ((sub_pair_right i j).trans hT) (f' j)
        = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f := by
    intro j T hT
    rw [← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]
  have h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j)
      - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
    intro j l
    refine hker {j, l} i _ (Finset.insert_nonempty _ _) ?_
    have hj : ({i, j} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_left j l)
    have hl : ({i, l} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_right j l)
    rw [map_sub, hcomp, hcomp, sub_eq_zero]
    have e1 := htriple j _ hj
    have e2 := htriple l _ hl
    exact e1.trans e2.symm
  choose n hn using h2
  set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'
  have hnN : ∀ j l, n j l ≤ N' := fun j l =>
    Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩
  · intro j l
    have h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j)
        - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
      rw [← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]
    show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j)
      = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)
    rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub]
    exact h0
  · have hii : ({i} : Finset ι) ⊆ {i, i} := sub_pair_left i i
    have hfi : f' i = x ^ K • f := by
      apply inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm
      rw [map_smul]
      exact hres i
    show x ^ N' • f' i = x ^ (N' + K) • f
    rw [hfi, smul_smul, ← pow_add]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHomLocPiecesCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_homLoc_pieces_compatible : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module (MvPolynomial ι A) M] [IsScalarTower A (MvPolynomial ι A) M] (ℳ : ℤ → Submodule A M) [PolyGradedSMul ι ℳ] [DirectSum.Decomposition ℳ] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S') (ev : ∀ I : Finset ι, I.Nonempty → M →ₗ[MvPolynomial ι A] P I), (∀ I hI, IsGradedMap ℳ (𝒢 I) (ev I hI)) → (∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) m, res I J h (ev I hI m) = ev J hJ m) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ I (hI : I.Nonempty) (m : M), ev I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0) → (∀ I (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : M), ev I hI m = xProd A I ^ l • f) → ∀ t : ℤ, ∃ φ : ∀ I : Finset ι, I.Nonempty → (homLoc ℳ I t →ₗ[A] 𝒢 I t), (∀ I hI, Function.Bijective (φ I hI)) ∧ ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : homLoc ℳ I t), (φ J hJ (homLocRes ℳ h t z) : P J) = res I J h (φ I hI z : P I) := by
  intro ι _ A _ M _ _ _ _ ℳ _ _ P _ _ _ _ 𝒢 _ _ res ev hgr hres hX hker hcok t
  have key : ∀ (I : Finset ι) (hI : I.Nonempty), ∃ φ : homLoc ℳ I t →ₗ[A] 𝒢 I t,
      Function.Bijective φ ∧ ∀ (z : homLoc ℳ I t) (k : ℕ) (m : M),
        awayFrac M (xProd A I) k m = z → xProd A I ^ k • (φ z : P I) = ev I hI m := by
    intro I hI
    exact exists_homLoc_bijective_of (hgr I hI) I
      (xProd_smul_bijective_of I fun i hi => hX i I hi)
      (fun _ y _ hy => hker I hI y hy) (fun _ a _ => hcok I hI a) t
  choose φ hφbij hφ using key
  refine ⟨φ, hφbij, ?_⟩
  intro I J hI hJ h z
  have hb : Function.Bijective fun x : P J => xProd A J • x :=
    xProd_smul_bijective_of J fun i hi => hX i J hi
  have hinj : ∀ (n : ℕ) (x y : P J), xProd A J ^ n • x = xProd A J ^ n • y → x = y := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
      intro x y hxy
      apply ih
      apply hb.1
      show xProd A J • (xProd A J ^ n • x) = xProd A J • (xProd A J ^ n • y)
      rw [← mul_smul, ← mul_smul, ← pow_succ']
      exact hxy
  obtain ⟨k, m, hkm⟩ := exists_awayFrac (z : LocalizedModule.Away (xProd A I) M)
  have hc : xProd A J = (∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) * xProd A I :=
    (Finset.prod_sdiff h).symm
  have hz : (homLocRes ℳ h t z : LocalizedModule.Away (xProd A J) M) =
      awayFrac M (xProd A J) k ((∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) ^ k • m) := by
    rw [coe_homLocRes, ← hkm]
    exact locRes_awayFrac MvPolynomial.X h (Finset.prod_sdiff h).symm k m
  have h1 := hφ I hI z k m hkm
  have h2 := hφ J hJ (homLocRes ℳ h t z) k _ hz.symm
  apply hinj k
  rw [h2, map_smul, ← hres I J hI hJ h m, ← h1, map_smul, ← mul_smul, ← mul_pow, hc]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem existsUnique_limit_of_dvd {R : Type*} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (z : ℕ → R)
    (hz : ∀ m, t ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃! x : R, ∀ m, t ^ (m + 1) ∣ x - z m := by
  have hmem : ∀ (n : ℕ) (a : R), a ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule R R) ↔ t ^ n ∣ a := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hchain : ∀ {m n : ℕ}, m ≤ n → t ^ m ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : t ^ m ∣ z (n + 1) - z n := (pow_dvd_pow t (by omega)).trans (hz n)
      have h2 := dvd_add h1 ih
      simpa using h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) z (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, hmem]
    exact hchain hmn)
  refine ⟨L, fun m => ?_, fun x hx => ?_⟩
  · have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
      have := hL (m + 1)
      rw [SModEq.comm, SModEq.sub_mem, hmem] at this
      exact this
    have h2 := dvd_add h1 (hz m)
    simpa using h2
  · have hLd : ∀ m, t ^ (m + 1) ∣ L - z m := by
      intro m
      have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
        have := hL (m + 1)
        rw [SModEq.comm, SModEq.sub_mem, hmem] at this
        exact this
      have h2 := dvd_add h1 (hz m)
      simpa using h2
    refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)
    rw [SModEq.zero, hmem]
    have h3 := dvd_sub (hx n) (hLd n)
    have h4 : t ^ (n + 1) ∣ x - L := by simpa using h3
    exact (pow_dvd_pow t (Nat.le_succ n)).trans h4

theorem isAdicComplete_span_tBdR (l : ℕ) [Fact l.Prime] :
    IsAdicComplete (Ideal.span {tBdR l}) (BdRp l) := by
  rw [← maximalIdeal_eq_span_tBdR]
  exact IsPerfectoidField.instIsAdicCompleteMaximalIdealBdR

theorem pInv_rangeRestrict (l : ℕ) [Fact l.Prime] (b : BdRp l) :
    pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b) = b :=
  RingEquiv.symm_apply_apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩) b

theorem pInv_injective (l : ℕ) [Fact l.Prime] : Function.Injective (pInv l) :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.injective

theorem existsUnique_bdRp_of_compatible (l : ℕ) [Fact l.Prime]
    (y : ∀ m : ℕ, Bk l (m + 1)) (hy : ∀ m, dk l (m + 1) (y (m + 1)) = y m) :
    ∃! x : BdRp l, ∀ m, pk l (m + 1) x = y m := by
  haveI := isAdicComplete_span_tBdR l
  choose z hz using fun m => Ideal.Quotient.mk_surjective (y m)
  have key : ∀ (m : ℕ) (x : BdRp l), pk l (m + 1) x = y m ↔ tBdR l ^ (m + 1) ∣ x - z m := by
    intro m x
    rw [← hz m, pk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hstep : ∀ m, tBdR l ^ (m + 1) ∣ z (m + 1) - z m := by
    intro m
    rw [← key m]
    have := hy m
    rw [← hz (m + 1)] at this
    exact this
  obtain ⟨x, hx, hu⟩ := existsUnique_limit_of_dvd (tBdR l) z hstep
  exact ⟨x, fun m => (key m x).2 (hx m), fun x' hx' => hu x' fun m => (key m x').1 (hx' m)⟩

theorem levSys_existsUnique {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    {M : ℕ} (h : LevHyp l K M) :
    ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) →
      ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  intro y hy
  obtain ⟨b, hb, hu⟩ := existsUnique_bdRp_of_compatible l y hy
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict b, fun m => ?_, fun x' hx' => ?_⟩
  · change pk l (m + 1) (pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b)) = y m
    rw [pInv_rangeRestrict]
    exact hb m
  · refine pInv_injective l ?_
    rw [pInv_rangeRestrict]
    exact hu _ hx'

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsXProdPowSmulEqEv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_xProd_pow_smul_eq_ev : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) → ∀ (I : Finset ι) (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : glue res), ev res I hI m = xProd A I ^ l • f := by
  intro ι _ A _ P _ _ _ _ res hcomp hsurj hfam I hI f
  classical
  obtain ⟨i, hi⟩ := hI
  have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.2 hi
  have key : ∀ (J : Finset ι) (hJ : {i} ∪ I = J) (g : P J),
      ∃ (l : ℕ) (a : P {i}), res {i} J (hJ ▸ Finset.subset_union_left) a = xProd A I ^ l • g := by
    intro J hJ
    subst hJ
    intro g
    obtain ⟨l, a, ha⟩ := hsurj I {i} g ⟨i, Finset.mem_singleton_self i⟩
    exact ⟨l, a, ha⟩
  obtain ⟨l, a, ha⟩ := key I (Finset.union_eq_right.2 hsub) f
  obtain ⟨c, N, hc, hci⟩ := hfam i a
  obtain ⟨q, hq⟩ : (MvPolynomial.X i : MvPolynomial ι A) ∣ xProd A I := by
    simpa [xProd] using Finset.dvd_prod_of_mem (fun j => (MvPolynomial.X j : MvPolynomial ι A)) hi
  refine ⟨N + l, q ^ N • ⟨c, mem_glue.2 hc⟩, ?_⟩
  rw [map_smul, ev_eq hcomp ⟨i, hi⟩ hi]
  change q ^ N • res {i} I hsub (c i) = _
  rw [hci, map_smul, show res {i} I hsub a = xProd A I ^ l • f from ha, hq, smul_smul, smul_smul,
    pow_add, mul_pow]
  congr 1
  ring

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsSwap
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen.Swap

section Abstract

variable {Γ G V V' : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coinv_of_intertwine (τ : Representation ℂ (Γ × G) V) (τ' : Representation ℂ (Γ × G) V')
    (ψ ψ' : Γ →* ℂˣ) (T : V ≃ₗ[ℂ] V') (θ : Γ →* Γ) (θ' : G →* G)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ')
    (hT : ∀ γ g v, T (τ (γ, g) v) = τ' (θ γ, θ' g) (T v)) (hψ : ∀ γ, ψ' (θ γ) = ψ γ)
    (h : HasFiniteLength (coinv τ' ψ')) : HasFiniteLength (coinv τ ψ) := by
  have key : ∀ (γ : Γ) (v : V), T (τ (γ, 1) v - (ψ γ : ℂ) • v) =
      τ' (θ γ, 1) (T v) - (ψ' (θ γ) : ℂ) • T v := fun γ v => by
    rw [map_sub, map_smul, hT, map_one, hψ]
  have hrel : (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).map (T : V →ₗ[ℂ] V') =
      twRel (τ'.comp (MonoidHom.inl Γ G)) ψ' := by
    unfold twRel
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨γ, v, rfl⟩, rfl⟩
      exact ⟨θ γ, T v, key γ v⟩
    · rintro ⟨γ', v', rfl⟩
      obtain ⟨γ, rfl⟩ := hθ γ'
      refine ⟨_, ⟨γ, T.symm v', rfl⟩, ?_⟩
      have := key γ (T.symm v')
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
  let E : (coinv τ ψ).Equiv ((coinv τ' ψ').comp θ' : Representation ℂ G _) :=
    Representation.Equiv.mk (Submodule.Quotient.equiv _ _ T hrel) fun g =>
      Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        show Submodule.Quotient.mk (T (τ (1, g) v)) = Submodule.Quotient.mk (τ' (1, θ' g) (T v))
        rw [hT, map_one])
  exact HasFiniteLength.of_equiv ((hasFiniteLength_comp_iff _ θ' hθ').2 h) E.symm

end Abstract

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : Type) [Fintype n] [DecidableEq n] : GL n k →* GL n k where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [transpose_mul])

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_invT (g : GL a k) : invT a (invT a g) = g := Units.ext (transpose_transpose _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_surjective : Function.Surjective (invT a : GL a k → GL a k) :=
  fun g => ⟨invT a g, invT_invT g⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_invT (g : GL a k) :
    GeneralLinearGroup.det (invT a g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  show ((g⁻¹).valᵀ).det = ((g⁻¹ : GL a k).val).det
  rw [det_transpose]

def trHomeo (a b : Type) : Matrix b a k ≃ₜ Matrix a b k where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

def trSB (a b : Type) : SB (Matrix b a k) ≃ₗ[ℂ] SB (Matrix a b k) where
  toFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo b a).continuous,
    Φ.2.2.comp_homeomorph (trHomeo b a)⟩
  invFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo a b).continuous,
    Φ.2.2.comp_homeomorph (trHomeo a b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))
  right_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))

theorem omChar_swap (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) :
    omChar b a μ (invT b h, invT a g) = omChar a b μ (g, h) := by
  simp only [omChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    detChar_apply, det_invT, MonoidHom.inv_apply, map_inv, neg_div, absPow_neg, inv_inv, mul_inv]
  exact mul_comm _ _

theorem trSB_omega (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) :
    trSB a b (omega a b μ (g, h) Φ) = omega b a μ (invT b h, invT a g) (trSB a b Φ) := by
  refine Subtype.ext (funext fun y => ?_)
  show (omChar a b μ (g, h) : ℂ) * Φ.1 (act yᵀ (g, h)) =
    (omChar b a μ (invT b h, invT a g) : ℂ) * Φ.1 (act y (invT b h, invT a g))ᵀ
  have e : act yᵀ (g, h) = (act y (invT b h, invT a g))ᵀ := by
    show (h⁻¹).val * yᵀ * g.val = (g.valᵀ * y * (h⁻¹).valᵀ)ᵀ
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [omChar_swap, e]

end Model

theorem coinv_swap_finiteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  intro k _ _ _ _ a b _ _ _ _ μ χ h
  refine coinv_of_intertwine _ _ _ _ (trSB a b) (invT b) (invT a) invT_surjective invT_surjective
    (fun γ g v => trSB_omega μ⁻¹ g γ v) (fun γ => ?_) h
  simp [det_invT]

end GlobalTheory.CompanionTheory.ThetaGLLen.Swap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftClosedEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_closed_embedding : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)) (e : ℕ) (i : Fin (m + 1)) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k : ℕ) (q : MvPolynomial (Fin (m + 1)) R) (t' : ℤ) (w : Tm I Y N D (d : ℤ) e t' {i}), w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) + GrSum.of (hc e {i}) t' w := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_projective_embedding_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerateStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_sections_generate : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureLocalBallStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_local_ball : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (k : ℕ) (a : Fv F v), lam ((fun z => z - a) ⁻¹' ballV v k) = ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | exact GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV | (intros; apply GlobalTheory.CompanionTheory.Equi.BallVol.measure_translate_ballV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturatedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_filtration_saturated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e) →
    (∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ n₀ : ℕ, ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Lift.uniform_lift | exact GlobalTheory.CompanionTheory.GE.Lift.uniform_lift | (intros; apply GlobalTheory.CompanionTheory.GE.Lift.uniform_lift <;> assumption)
end

