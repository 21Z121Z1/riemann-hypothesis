import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0380
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEisensteinLatticeBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LocalizedLatticeBasis

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem l_ne_zero : (l : bk.S) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x => bk.str.symm (Ideal.Quotient.mk _ x)) h
  simp only [map_natCast, map_zero] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2

theorem isDomain_loc : IsDomain (Localization.Away (l : bk.S)) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

theorem inj_loc : Function.Injective (algebraMap bk.S (Localization.Away (l : bk.S))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

theorem clear {α β : Type} [Fintype α] [Fintype β]
    (A : Matrix α β (Localization.Away (l : bk.S))) :
    ∃ k : ℕ, ∀ j, k ≤ j → ∃ A₀ : Matrix α β bk.S,
      A₀.map (algebraMap bk.S (Localization.Away (l : bk.S))) =
        (algebraMap bk.S (Localization.Away (l : bk.S)) (l : bk.S)) ^ j • A := by
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers (l : bk.S))
    (Finset.univ : Finset (α × β)) (fun p => A p.1 p.2)
  obtain ⟨k, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hb
  refine ⟨k, fun j hj => ?_⟩
  have h' : ∀ p : α × β, ∃ s : bk.S, algebraMap bk.S _ s = ((l : bk.S) ^ k) • A p.1 p.2 := by
    intro p
    obtain ⟨s, hs⟩ := h p (Finset.mem_univ _)
    exact ⟨s, hs⟩
  choose s hs using h'
  refine ⟨Matrix.of fun i i' => (l : bk.S) ^ (j - k) * s (i, i'), ?_⟩
  ext i i'
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, map_mul, map_pow, hs, smul_eq_mul,
    Algebra.smul_def]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

theorem pid_basis {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (d m : ℕ)
    (Y : Matrix (Fin d) (Fin m) R) (e : R) (he : e ≠ 0) :
    ∃ (X X' Rm : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin m) (Fin d) R) (Q' : Matrix (Fin d) (Fin m) R),
      X = Y * Q + e • Rm ∧ Y = X * Q' ∧ X * X' = e • (1 : Matrix (Fin d) (Fin d) R) := by
  classical
  let g : Fin m ⊕ Fin d → (Fin d → R) := fun s => Sum.elim (fun k i => Y i k) (fun j => e • Pi.single j 1) s
  let N : Submodule R (Fin d → R) := Submodule.span R (Set.range g)
  obtain ⟨k, bN⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin d)) N
  have gmem : ∀ s, g s ∈ N := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hk : k = d := by
    apply le_antisymm
    · have h1 := Submodule.finrank_le N
      rw [Module.finrank_eq_card_basis bN, Module.finrank_fin_fun] at h1
      simpa using h1
    · have hli : LinearIndependent R (fun j : Fin d => (⟨g (Sum.inr j), gmem _⟩ : N)) := by
        apply LinearIndependent.of_comp N.subtype
        change LinearIndependent R (fun j : Fin d => e • (Pi.single j (1 : R) : Fin d → R))
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have := congrFun hc i
        simp [Finset.sum_apply, Pi.single_apply] at this
        exact (this.resolve_right he)
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis bN] at h1
      simpa using h1
  subst hk
  have hc : ∀ j, ∃ c : Fin m ⊕ Fin k → R, ∑ s, c s • g s = (bN j : Fin k → R) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (bN j).2
  choose c hc using hc
  have hr : ∀ s (i : Fin k), g s i = ∑ j, bN.repr ⟨g s, gmem s⟩ j * (bN j : Fin k → R) i := by
    intro s i
    have h := congrArg (fun x : N => (x : Fin k → R) i) (bN.sum_repr ⟨g s, gmem s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  refine ⟨Matrix.of fun i j => (bN j : Fin k → R) i, Matrix.of fun j i => bN.repr ⟨g (Sum.inr i), gmem _⟩ j,
    Matrix.of fun i j => c j (Sum.inr i), Matrix.of fun i j => c j (Sum.inl i),
    Matrix.of fun j i => bN.repr ⟨g (Sum.inl i), gmem _⟩ j, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, g, Sum.elim_inl,
      Sum.elim_inr, Pi.single_apply] at h
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, ← h]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [show Y i i' = g (Sum.inl i') i from rfl, hr]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := hr (Sum.inr i') i
    simp only [g, Sum.elim_inr, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

theorem matMapSmul {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {α β : Type} (s : S) (M : Matrix α β S) :
    (s • M).map f = f s • M.map f := by
  ext i j; simp

open Matrix in

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m n : ℕ)
    (Y : Matrix (Fin d) (Fin m) (bk.S)), ∃ (c : ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S))
    (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)),
    X * X' = ((l : bk.S) ^ c * bk.E ^ n) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ X = Y * Q + bk.E ^ n • R ∧
      (l : bk.S) ^ c • Y = X * Q' := by
  intro l _ K bk d m n Y
  haveI := isDomain_loc bk
  haveI := GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime l K bk
  set φ := algebraMap bk.S (Localization.Away (l : bk.S)) with hφ
  have hE : φ (bk.E ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ (inj_loc bk)]; exact pow_ne_zero _ bk.E_ne_zero
  obtain ⟨Xb, X'b, Rb, Qb, Q'b, h1, h2, h3⟩ := pid_basis d m (Y.map φ) (φ (bk.E ^ n)) hE
  obtain ⟨k1, c1⟩ := clear bk Qb
  obtain ⟨k2, c2⟩ := clear bk Rb
  obtain ⟨k3, c3⟩ := clear bk Q'b
  obtain ⟨k4, c4⟩ := clear bk X'b
  obtain ⟨Q0, hQ0⟩ := c1 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨R0, hR0⟩ := c2 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨Q'0, hQ'0⟩ := c3 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨X'0, hX'0⟩ := c4 (k1 + k2 + k3 + k4) (by omega)
  rw [← hφ] at hQ0 hR0 hQ'0 hX'0
  set c0 := k1 + k2 + k3 + k4
  have hinj : Function.Injective fun M : Matrix (Fin d) (Fin d) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hinj' : Function.Injective fun M : Matrix (Fin d) (Fin m) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hX : (Y * Q0 + bk.E ^ n • R0).map φ = φ (l : bk.S) ^ c0 • Xb := by
    rw [Matrix.map_add φ (map_add φ), Matrix.map_mul, matMapSmul, hQ0, hR0, h1, smul_add, Matrix.mul_smul, smul_comm]
  refine ⟨2 * c0, Y * Q0 + bk.E ^ n • R0, X'0, R0, Q0, Q'0, ?_, rfl, ?_⟩
  · apply hinj
    simp only
    rw [Matrix.map_mul, hX, hX'0, Matrix.smul_mul, Matrix.mul_smul, h3, matMapSmul, Matrix.map_one _ (map_zero φ) (map_one φ),
      smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_pow]
    ring
  · apply hinj'
    simp only
    rw [Matrix.map_mul, hX, hQ'0, Matrix.smul_mul, Matrix.mul_smul, ← h2, matMapSmul, smul_smul, map_pow, two_mul, pow_add]

end GlobalTheory.BSP.LocalizedLatticeBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isInternal_map_of_corner {K : Type} [Field K] {n t : ℕ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hV : DirectSum.IsInternal Vs) (hba : b * a = 1)
    (he : ∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) :
    DirectSum.IsInternal (fun j => (Vs j).map b.mulVecLin) := by
  classical
  have hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w := fun w => by
    simp [Matrix.mulVec_mulVec, hba]
  have hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin := Matrix.mulVecLin_mul a b

  have hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S →
      (S.map b.mulVecLin).map a.mulVecLin ≤ S := by
    intro S hS
    rwa [← Submodule.map_comp, ← hE]
  have hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j := by
    rintro j _ ⟨v, hv, rfl⟩
    exact he j v hv
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hV ⊢
  obtain ⟨hind, htop⟩ := hV
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro j
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k := by
      simp_rw [Submodule.map_iSup]
      exact iSup₂_mono fun k _ => hVj k
    have hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin := by
      simp_rw [Submodule.map_iSup]
      exact hx2
    have h1 : a.mulVecLin x ∈ Vs j := hback _ (hVj j) (Submodule.mem_map_of_mem hx1)
    have h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k :=
      hback _ hrest (Submodule.mem_map_of_mem hx2')
    rw [← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]
  · rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
    exact fun w => ⟨a.mulVecLin w, hfg w⟩

theorem exists_separable_charpoly_of_isInternal {K : Type} [Field K] [Infinite K] {t : ℕ}
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin t → K))
    (hW : DirectSum.IsInternal W) :
    ∃ D : Matrix (Fin t) (Fin t) K, (∀ j, ∀ w ∈ W j, D.mulVec w ∈ W j) ∧
      D.charpoly.Separable := by
  classical

  let v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j) := fun j => Module.finBasis K (W j)
  let B := hW.collectedBasis v
  let μ : (Σ j, Fin (Module.finrank K (W j))) → K :=
    fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)
  have hμ : Function.Injective μ :=
    (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)
  let φ : (Fin t → K) →ₗ[K] (Fin t → K) := B.constr K (fun s => μ s • B s)
  have hφB : ∀ s, φ (B s) = μ s • B s := fun s => B.constr_basis K _ s
  refine ⟨LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro j w hw
    have hD : (LinearMap.toMatrix' φ).mulVec w = φ w := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K) := by
      rw [(v j).sum_repr]
    rw [hD, hw', Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩ := by simp [B]
    rw [hk, hφB]
    exact Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)
  · have h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly := by
      rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
    have h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ := by
      ext s s'
      rw [LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hμ

theorem exists_corner_separable_charpoly :
    ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  intro K _ _ n t ι _ _ Vs a b hV hba he
  obtain ⟨D, hD, hsep⟩ :=
    exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)
  refine ⟨a * D * b, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hu'⟩ := hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)
    have hm : (a * D * b).mulVec v = (a * b).mulVec u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      exact hu'.symm
    rw [hm]
    exact he j u hu
  · have hc : b * (a * D * b) * a = D := by
      calc b * (a * D * b) * a = (b * a) * D * (b * a) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hba, Matrix.one_mul, Matrix.mul_one]
    rw [hc]
    exact hsep

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedDegree

theorem exists_degree : ∀ (l : ℕ) [Fact l.Prime],
    (∀ n : ℕ, 0 < n → ∀ σ : GQ l, ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
    (∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) → a ≡ b [MOD n]) →
    ∃ z : GQ l → ℤ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
      ∀ (σ : GQ l) (a : ℕ), (∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
        z σ = (a : ℤ_[l]) := by
  intro l hl h1 h2
  have hpos : ∀ k : ℕ, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  choose a ha using fun (σ : GQ l) (k : ℕ) => h1 (l ^ k) (hpos k) σ
  have hdv : ∀ (σ : GQ l) (k : ℕ), (l : ℤ) ^ k ∣ (a σ (k + 1) : ℤ) - (a σ k : ℤ) := by
    intro σ k
    have h := h2 (l ^ k) (a σ k) (a σ (k + 1)) (hpos k) fun x hx => by
      rw [← ha σ k x hx, ← ha σ (k + 1) x (by
        rw [pow_succ l k]; exact GlobalTheory.UnramifiedCrys.pow_pow_mul hx l)]
    exact_mod_cast h.dvd
  obtain ⟨z, hz⟩ : ∃ z : GQ l → ℤ_[l], ∀ σ k, PadicInt.toZModPow k (z σ) = (a σ k : ZMod (l ^ k)) := by
    refine ⟨fun σ => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ)), fun σ k => ?_⟩
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ) k,
      Int.cast_natCast]
  have key : ∀ (σ : GQ l) (k b : ℕ), (∀ x : Om l, x ^ l ^ l ^ k = x → σ x = x ^ l ^ b) →
      PadicInt.toZModPow k (z σ) = (b : ZMod (l ^ k)) := by
    intro σ k b hb
    rw [hz, ZMod.natCast_eq_natCast_iff]
    exact h2 _ _ _ (hpos k) fun x hx => by rw [← ha σ k x hx, hb x hx]
  refine ⟨z, ?_, fun σ τ => ?_, fun σ b hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have hev : ∀ᶠ σ in 𝓝 σ₀, ∀ x ∈ {y : Om l | y ^ l ^ l ^ k = y}, σ x = σ₀ x := by
      refine (GlobalTheory.UnramifiedCrys.finite_fixedPow (p := l) (R := Om l) (hpos k)).eventually_all.2
        fun x _ => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).preimage
        (continuous_mul_left σ₀⁻¹)
      filter_upwards [ho.mem_nhds (show σ₀ ∈ _ by simp)] with σ hσ
      have h : σ₀⁻¹ (σ x) = x := hσ
      have h' := congrArg σ₀ h
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
    filter_upwards [hev] with σ hσ
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero, hz σ₀]
    exact key σ k _ fun x hx => by rw [hσ x hx, ha σ₀ k x hx]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_add, hz σ, hz τ, ← Nat.cast_add]
    refine key _ k _ fun x hx => ?_
    rw [AlgEquiv.mul_apply, ha τ k x hx, map_pow, ha σ k x hx, ← pow_mul, ← pow_add]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_natCast]
    exact key σ k b (hb _ (hpos k))

end GlobalTheory.UnramifiedDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

open Polynomial

theorem isLocalRing_of_domain_finite_padicInt (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B]
    [IsDomain B] [Algebra ℤ_[l] B] [Module.Finite ℤ_[l] B] : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨E, hE, hM⟩ := GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  have e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l] := hM _ 0 fun n => by
    simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact dvd_pow_self b (Nat.succ_ne_zero n)
  have e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l] := hM _ 1 fun n => by
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    have := one_sub_dvd_one_sub_pow b (n + 1)
    rw [← neg_sub 1 (b ^ (n + 1))]
    exact this.neg_right
  simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h
  · rw [h, zero_sub] at e1
    exact h1 (isUnit_of_dvd_one (dvd_neg.1 e1))
  · rw [h] at e0
    exact h0 (isUnit_of_dvd_one e0)

theorem exists_fin_prod_of_splits {L : Type} [Field L] (t : ℕ) (f : L[X]) (hs : f.Splits)
    (hm : f.Monic) (ht : f.natDegree = t) : ∃ α : Fin t → L, f = ∏ c, (X - C (α c)) := by
  have hc : f.roots.toList.length = t := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]
  subst hc
  refine ⟨f.roots.toList.get, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get f.roots.toList]
  rw [List.map_ofFn]
  rfl

theorem exists_finite_dvr_splitting : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  intro l _ A ι _ _ _ _ _ _ _ t P hP
  classical
  haveI := Fintype.ofFinite ι
  let K := FractionRing A
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  let F : K[X] := ∏ i, (P i).map (toFr A)
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => (hP i).1
  let L := F.SplittingField
  haveI : IsScalarTower A K L := inferInstance
  let S := integralClosure A L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S
  haveI : IsLocalRing S := by
    letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra
    haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S
    exact isLocalRing_of_domain_finite_padicInt l S
  have hinj : Function.Injective (algebraMap A S) :=
    algebraMap_injective_of_field_isFractionRing A S K L
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1
    (inferInstance : IsDedekindDomain S)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj,
    fun i => ?_⟩
  let e : L ≃ₐ[S] FractionRing S := (FractionRing.algEquiv S L).symm
  have hsF : (F.map (algebraMap K L)).Splits := SplittingField.splits F
  have hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits :=
    hsF.of_dvd (hF.map _).ne_zero
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hcomp : (toFr S).comp (algebraMap A S) =
      ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A) := by
    ext a
    have : algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a) := by
      rw [← IsScalarTower.algebraMap_apply A S L]
      exact (IsScalarTower.algebraMap_apply A K L a).symm
    simp only [RingHom.comp_apply, this]
    exact (e.commutes _).symm
  rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
  refine exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_
  rw [natDegree_map, natDegree_map, (hP i).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiltrationAdaptedBasisOfSubspaceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filtration_adapted_basis_of_subspace : ∀ {k M : Type} [Field k] [AddCommGroup M] [Module k M] (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M), Antitone F → (∀ x ∈ D, ∃ a, x ∈ F a) → (∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) → ∃ (b : Module.Basis (Fin (Module.finrank k D)) k D) (h : Fin (Module.finrank k D) → ℤ), (∀ j, (b j : M) ∈ F (h j) ∧ (b j : M) ∉ F (h j + 1)) ∧ ∀ (a : ℤ) (x : D), (x : M) ∈ F a → ∀ j, b.repr x j ≠ 0 → a ≤ h j := by
  first | exact @GlobalTheory.AdaptedBasis.exists_adapted_basis | exact GlobalTheory.AdaptedBasis.exists_adapted_basis | (intros; apply GlobalTheory.AdaptedBasis.exists_adapted_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProductOrientedBoundedPrismsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_product_oriented_boundedPrisms : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∃ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) ∧ (∀ x, x ∈ Q.I ↔ ∀ i, (π i).f x ∈ (C i).I) ∧ ∀ (Z : Obj l R) (a : ∀ i, Hom Z (C i)), ∃ c : Hom Z Q, ∀ i, (π i).comp c = a i := by
  first | exact @GlobalTheory.Prism.finite_product_oriented | exact GlobalTheory.Prism.finite_product_oriented | (intros; apply GlobalTheory.Prism.finite_product_oriented <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicCompleteStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type) [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P) (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  first | exact @GlobalTheory.BSP.LiftProj.exists_lift | exact GlobalTheory.BSP.LiftProj.exists_lift | (intros; apply GlobalTheory.BSP.LiftProj.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixFCrystalBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  first | exact @GlobalTheory.BSP.frob_matrix_bk | exact GlobalTheory.BSP.frob_matrix_bk | (intros; apply GlobalTheory.BSP.frob_matrix_bk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMemStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' : ∀ (l : ℕ) [Fact l.Prime] {R : Type} [Ring R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R), ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R), (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  first | exact @GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | exact GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem | (intros; apply GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisOfIsDeRhamLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_basis_of_isDeRham_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∃ x : Fin d → Fin d → P.R.BdR, LinearIndependent ↥K.1 x ∧ (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) ∧ ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ∈ Submodule.span ↥K.1 (Set.range x) := by
  first | exact @GlobalTheory.DRMat.invariant_basis_of_isDR | exact GlobalTheory.DRMat.invariant_basis_of_isDR | (intros; apply GlobalTheory.DRMat.invariant_basis_of_isDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrameStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  first | (exact @GlobalTheory.BcrisInv.invariant_unit) | (exact GlobalTheory.BcrisInv.invariant_unit) | (intros; apply GlobalTheory.BcrisInv.invariant_unit  <;> assumption)
end

