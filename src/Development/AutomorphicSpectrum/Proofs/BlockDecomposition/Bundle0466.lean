import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowUnifLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.TranslAdele

theorem thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  ext i j
  change σ (σ (g.val i j)) = g.val i j
  exact hσ _

theorem exists_scalar_of_central {K : Type} [Field K] {n : ℕ} (z : GL (Fin n) K)
    (hz : ∀ h : GL (Fin n) K, z * h = h * z) : ∃ c : K, z.val = Matrix.scalar (Fin n) c := by
  have : z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have h := hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have h' := congrArg Units.val h
    exact h'.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem Phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map f = GlobalTheory.Tw.Phi n S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translAd : TranslAd := by
  intro E _ _ _ n u hu g

  have hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u) := by
    intro h
    have hinv : thetaE E n (thetaE E n h) = h :=
      thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h
    have h1 := hu.1 (thetaE E n h)
    rw [hinv] at h1
    have h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
      have := thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)
      rw [show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv] at this
      exact this
    rw [h2] at h1
    have h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h := by
      have h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h := by rw [h1]; group
      calc h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹ * u) := by group
        _ = (PhiU n E)⁻¹ * u * h := by rw [h4]; group
    rw [← h3, mul_assoc h]
  obtain ⟨c, hc⟩ := exists_scalar_of_central _ hz

  set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw
  have hwc : ∀ t : GA E n, w * t = t * w := by
    intro t
    apply Units.ext
    have hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c) := by
      have : w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E)) := rfl
      rw [this, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [Units.val_mul, Units.val_mul, hval]
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) _
  have hP : ratGL E n (PhiU n E) = PhiU n (Ad E) := by
    apply Units.ext
    rw [phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]
    rfl
  have hr : ratGL E n u = PhiU n (Ad E) * w := by
    rw [hw, map_mul, map_inv, hP, mul_inv_cancel_left]
  rw [thetaGL_eq, hr]
  have h5 : w * thetaA E n g * w⁻¹ = thetaA E n g := by rw [hwc]; group
  calc PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹
      = PhiU n (Ad E) * (w * thetaA E n g * w⁻¹) * (PhiU n (Ad E))⁻¹ := by rw [h5]
    _ = PhiU n (Ad E) * w * thetaA E n g * (PhiU n (Ad E) * w)⁻¹ := by group

end GlobalTheory.CompanionTheory.TranslAdele

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetween
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisActionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_galois_action : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | exact GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | (intros; apply GlobalTheory.CompanionTheory.LTHodge.UnitAct.main <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsValueSubset
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial GlobalTheory.CompanionTheory.LbElem.MonomialInJ GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

namespace GlobalTheory.CompanionTheory.LbElem.JPredDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_diag_mul {N : ℕ} {a b : GL (Fin N) k} (n : GL (Fin N) k) {α β : Fin N → k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = Matrix.diagonal α)
    (hb : (b : Matrix (Fin N) (Fin N) k) = Matrix.diagonal β) (i j : Fin N) :
    ((a * n * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      α i * (n : Matrix (Fin N) (Fin N) k) i j * β j := by
  rw [Units.val_mul, Units.val_mul, ha, hb, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diag_ne_zero {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (i : Fin N) : d i ≠ 0 := by
  have h := diag_ne_zero_of_offDiag x (fun i j hij => by rw [hx, Matrix.diagonal_apply_ne _ hij]) i
  rwa [hx, Matrix.diagonal_apply_eq] at h

theorem val_inv_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) :
    ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
  have h1 : (x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [hx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (diag_ne_zero hx i)
  calc ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
          ((x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹)) := by rw [h1, mul_one]
    _ = Matrix.diagonal fun i => (d i)⁻¹ := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem val_pow_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (r : ℕ) :
    ((x ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => d i ^ r := by
  rw [Units.val_pow_eq_pow_val, hx, Matrix.diagonal_pow]
  rfl

theorem val_conj_up (a b c : k) (r : ℕ) :
    valuation k (a ^ r * c * (b ^ r)⁻¹) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [map_mul, map_mul, map_inv₀, map_pow, map_pow, div_pow, div_eq_mul_inv, mul_right_comm]

theorem val_conj_lo (a b c : k) (r : ℕ) :
    valuation k ((b ^ r)⁻¹ * c * a ^ r) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [← val_conj_up]
  congr 1
  ring

theorem up_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, j < i → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, j < i → ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k (((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d i) / valuation k (d j)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hp hq
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_up _ _ _ r

theorem lo_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, i < j → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, i < j → (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k ((((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d j) / valuation k (d i)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hq hp
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact inv_mul_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_lo _ _ _ r

theorem ratio_lt_one {a b : ValueGroupWithZero k} (h : a < b) : a / b < 1 :=
  (div_lt_one₀ (lt_of_le_of_lt zero_le' h)).2 h

theorem exists_contract {N : ℕ} {d : Fin N → k} (hd : ∀ i, d i ≠ 0)
    (hinc : ∀ i j : Fin N, i < j → valuation k (d i) < valuation k (d j))
    {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ℕ, ∀ i j : Fin N, i < j → (valuation k (d i) / valuation k (d j)) ^ r < γ := by
  classical
  have h : ∀ p : Fin N × Fin N, ∃ r : ℕ, p.1 < p.2 → ∀ r' : ℕ, r ≤ r' →
      (valuation k (d p.1) / valuation k (d p.2)) ^ r' < γ := by
    intro p
    by_cases hp : p.1 < p.2
    · have h1 := ratio_lt_one (hinc _ _ hp)
      have h2 : valuation k (d p.1) / valuation k (d p.2) ≠ 0 :=
        div_ne_zero ((Valuation.ne_zero_iff _).2 (hd _)) ((Valuation.ne_zero_iff _).2 (hd _))
      obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt h2 h1 hγ
      exact ⟨m + 1, fun _ r' hr' => lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' h1.le hr') hm⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun i j hij => hf (i, j) hij _ (Finset.le_sup (Finset.mem_univ _))⟩

theorem levi_comm {N : ℕ} (s x : Levi k (Bl (ones N))) : s * x = x * s := by
  funext a
  haveI : Subsingleton (Fin (ones N a)) := by
    show Subsingleton (Fin 1)
    infer_instance
  apply Units.ext
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  simp only [Units.val_mul, Matrix.mul_apply, Pi.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem torEmb_diag {N : ℕ} (s : Levi k (Bl (ones N))) :
    ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact tor_offDiag (⟨s, rfl⟩ : torEmb k N s ∈ Tor k N) h

theorem sub_one_le {N : ℕ} {x : GL (Fin N) k} {γ : ValueGroupWithZero k}
    (h1 : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i = 1)
    (h2 : ∀ i j, i ≠ j → valuation k ((x : Matrix (Fin N) (Fin N) k) i j) ≤ γ) (i j : Fin N) :
    valuation k ((x : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ := by
  by_cases h : i = j
  · subst h
    rw [h1, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le'
  · rw [Matrix.one_apply_ne h, sub_zero]
    exact h2 i j h

theorem exists_value_subset {N : ℕ} {U : Set (GL (Fin N) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ g : GL (Fin N) k, (∀ i j,
      valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ) → g ∈ U := by
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2 Zls.irreducible_unif.ne_zero
  obtain ⟨M, -, hsub⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_congruence_subset k N _ hne
    GlobalTheory.CompanionTheory.CongruenceBasis.val_unif_lt_one GlobalTheory.CompanionTheory.CongruenceBasis.val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨_, (Valuation.ne_zero_iff _).2 (pow_ne_zero M hne), fun g hg => hsub hg⟩

end GlobalTheory.CompanionTheory.LbElem.JPredDom

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWittComplementFrame
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_coords {K : Type} [Field K] {n : ℕ} (S : Submodule K (Fin n → K)) (P : Matrix (Fin n) (Fin n) K)
    (hP : ∀ v, P *ᵥ v ∈ S) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K),
      (∀ w, Z *ᵥ w ∈ S) ∧ Z * C = P ∧ Function.Injective Z.mulVec := by
  classical
  let b := Module.finBasis K S
  let Z : Matrix (Fin n) (Fin (Module.finrank K S)) K := Matrix.of fun i k => (b k : Fin n → K) i
  have hZ : ∀ w, Z *ᵥ w = ((∑ k, w k • b k : S) : Fin n → K) := by
    intro w
    ext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm, Submodule.coe_sum, Finset.sum_apply]
  let L : (Fin n → K) →ₗ[K] S := P.mulVecLin.codRestrict S hP
  let c : (Fin n → K) →ₗ[K] (Fin (Module.finrank K S) → K) := b.equivFun.toLinearMap ∘ₗ L
  refine ⟨_, Z, LinearMap.toMatrix' c, fun w => by rw [hZ]; exact Subtype.property _, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hZ]
    have : (∑ k, c v k • b k : S) = L v := b.sum_equivFun (L v)
    rw [this]
    rfl
  · intro w w' h
    rw [hZ, hZ] at h
    have h' := Subtype.coe_injective h
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h'
    exact b.equivFun.symm.injective h'

theorem exists_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  have hc : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => sigma_sigma hσ _
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := hA ▸ hW.xx
  have hBY : B * Y = 0 := hB ▸ hW.yy
  have hAY : A * Y = 1 := hA ▸ hW.xy
  have hBX : B * X = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hc, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
    rw [hB, h]
  obtain ⟨P, hPd⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAP : A * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hBP : B * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, hBY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBX, hAX,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPY : P * Y = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBY, hAY,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  obtain ⟨m, Z, C, hS, hZC, hinj⟩ := exists_coords
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) P (fun v => by
      refine ⟨?_, ?_⟩
      · simp [Matrix.mulVec_mulVec, hAP]
      · simp [Matrix.mulVec_mulVec, hBP])
  have hAZ : A * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).1
  have hBZ : B * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).2
  have hcan : ∀ {ι : Type} (M M' : Matrix (Fin m) ι E), Z * M = Z * M' → M = M' := by
    intro ι M M' h
    ext i j
    exact congrFun (hinj (a₁ := fun i => M i j) (a₂ := fun i => M' i j)
      (funext fun a => congrFun (congrFun h a) j)) i
  have hPZ : P * Z = Z := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBZ, hAZ,
      Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hCZ : C * Z = 1 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPZ, Matrix.mul_one])
  have hCX : C * X = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPX, Matrix.mul_zero])
  have hCY : C * Y = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPY, Matrix.mul_zero])
  refine ⟨m, Z, Matrix.fromRows B (Matrix.fromRows C A), hA ▸ hAZ, hB ▸ hBZ, ?_, ?_⟩
  · rw [frm, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      hBX, hBZ, hBY, hCX, hAX, hCZ, hCY, hAZ, hAY]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  · rw [frm, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, hZC, hPd]
    abel

end GlobalTheory.CompanionTheory.CFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSphNe
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Function
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitaryWord

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.U

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev unitFn (n : ℕ) (w : Pl E) : UL n w → ℂ := (KL n w : Set (UL n w)).indicator 1

theorem isHecke_zero {w : Pl E} (K' : Subgroup (UL n w)) : IsHecke K' (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isHecke_lone (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    IsHecke K' (lone K') :=
  (hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1

theorem isHecke_lconv (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {f₁ f₂ : UL n w → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) : IsHecke K' (lconv f₁ f₂) :=
  (hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1

theorem lone_KL (w : Pl E) : lone (KL n w) = unitFn n w := by
  simp [lone, unitFn, Subgroup.relIndex_self]
  rfl

theorem isHecke_lpow (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (lpow K' g k) := by
  induction k with
  | zero => exact isHecke_lone hL hK
  | succ k ih => exact isHecke_lconv hL hK hg ih

section Fam

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  (F : UFam S lam K') {B : Finset (Pl E)}

end Fam

end GlobalTheory.CompanionTheory.UnitaryWord

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanishStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_restriction_of_bdsq_vanish : PositivityTheory.RgBcC.RealD.BdSqL → PositivityTheory.RgBcC.RealD.VanKL → PositivityTheory.RgBcC.RealD.InjRL := by
  first | exact @GlobalTheory.CompanionTheory.InjRL.injRL_of | exact GlobalTheory.CompanionTheory.InjRL.injRL_of | (intros; apply GlobalTheory.CompanionTheory.InjRL.injRL_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHoldsStatement
section
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_algebra_holds : LocAlg := by
  first | exact @GlobalTheory.CompanionTheory.LocHecke.locAlg | exact GlobalTheory.CompanionTheory.LocHecke.locAlg | (intros; apply GlobalTheory.CompanionTheory.LocHecke.locAlg <;> assumption)
end

