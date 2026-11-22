import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0242
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorization
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecomposition
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0241
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0214
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0209
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WavePairingTimeSymmetry

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowToColumnReduction
section
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinRow

def posFn {m : ℕ} (j o : ℕ) : Fin m ⊕ Fin j → ℕ
  | .inl a => if (a : ℕ) < o then a else a + j
  | .inr w => o + w

theorem posFn_lt {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) : posFn j o x < N := by
  rcases x with a | w
  · have := a.2
    simp only [posFn]
    split_ifs <;> omega
  · have := w.2
    simp only [posFn]
    omega

theorem posFn_injective {m j o : ℕ} (ho : o ≤ m) :
    Function.Injective (posFn j o : Fin m ⊕ Fin j → ℕ) := by
  rintro (a | w) (b | w') hxy <;> simp only [posFn] at hxy
  · have : (a : ℕ) = b := by split_ifs at hxy <;> omega
    exact congrArg _ (Fin.ext this)
  · have := w'.2
    exfalso
    split_ifs at hxy <;> omega
  · have := w.2
    exfalso
    split_ifs at hxy <;> omega
  · exact congrArg _ (Fin.ext (by omega))

def eo {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) : Fin m ⊕ Fin j ≃ Fin N :=
  Equiv.ofBijective (fun x => ⟨posFn j o x, posFn_lt h ho x⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y hxy => posFn_injective ho (congrArg Fin.val hxy), ?_⟩
    simp [h])

theorem eo_val {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) :
    ((eo h ho x : Fin N) : ℕ) = posFn j o x := rfl

section Pull

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem col_pat {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => colPat N j (eo h ho x) (eo h ho y)) = chainPat m j 0 := by
  funext x y
  apply propext
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [colPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem col_E {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => cutE K N j (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [cutE, eo_val, posFn, chainE] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem row_pat {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowPat N k a (eo h ho x) (eo h ho y)) = chainPat m j a := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem row_E {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowE K N k a (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem j_pat {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jPat N kk s (eo h ho x) (eo h ho y)) = chainPat m kk s := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem j_E {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jE K N kk s (eo h ho x) (eo h ho y)) = chainE K m kk := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem wh_eq_col (hS : St.WhSym) (hC : St.ChainIndep) {m j N o t : ℕ} (h : m + j = N) (ho : o ≤ m)
    (ht : t < m) (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (χ : GL (Fin N) K → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) {Φ : Fin N → Fin N → Prop} {E : Fin N → Fin N → K}
    (hΦ : (fun x y => Φ (eo h ho x) (eo h ho y)) = chainPat m j t)
    (hE : (fun x y => E (eo h ho x) (eo h ho y)) = chainE K m j) :
    wh Φ E ψ₀ χ = wh (colPat N j) (cutE K N j) ψ₀ χ := by
  have h0 : 0 ≤ m := Nat.zero_le m
  have s1 := (hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).1 (eo h ho)
  have s2 := (hS K (Fin m ⊕ Fin j) (Fin N) (colPat N j) (cutE K N j) ψ₀ χ).1 (eo h h0)
  have c := ((hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).2 hχ).1 (eo h ho) (eo h h0)
  rw [hΦ, hE] at s1
  rw [col_pat h h0, col_E K h h0] at s2
  rw [← s1, ← s2, show (fun x => χ (glEquiv K (eo h ho) x)) = fun x => χ (glEquiv K (eo h h0) x)
    from funext c]
  refine hC K m j t ψ₀ _ hψ (fun x g => ?_) ht
  simp only [map_mul, map_inv]
  exact hχ _ _

theorem rowToCol_of (hS : St.WhSym) (hC : St.ChainIndep) : St.RowToCol := by
  intro K _ _ _ N ψ₀ χ hψ hχ
  refine ⟨fun k a hak hkN => ?_, fun kk s hN => ?_⟩
  · have h : (N - (k - 1 - a)) + (k - 1 - a) = N := by omega
    have ho : a + 1 ≤ N - (k - 1 - a) := by omega
    have hk : k = a + 1 + (k - 1 - a) := by omega
    exact wh_eq_col K hS hC h ho (t := a) (by omega) ψ₀ hψ χ hχ (row_pat h ho hk) (row_E K h ho hk)
  · have h : (2 * s + 1) + kk = N := by omega
    have ho : s ≤ 2 * s + 1 := by omega
    exact wh_eq_col K hS hC h ho (t := s) (by omega) ψ₀ hψ χ hχ (j_pat h ho) (j_E K h ho)

end Pull

theorem rowToCol : St.RowToCol := rowToCol_of GlobalTheory.T.whittaker_symmetry GlobalTheory.T.chain_independence

end GlobalTheory.CompanionTheory.TyFinRow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.EmbUniq

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_algHom {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have a := minpoly.algHom_eq (L.1.val.comp τ) (RingHom.injective (L.1.val.comp τ : ↥K.1 →+* Om l)) x
  have b := minpoly.algHom_eq K.1.val (RingHom.injective (K.1.val : ↥K.1 →+* Om l)) x
  have c : minpoly ℚ_[l] ((τ x : ↥L.1) : Om l) = minpoly ℚ_[l] (x : Om l) := a.trans b.symm
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, c]

theorem norm_le_one_of_isIntegral {x : Om l} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Om l)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Om l))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

variable {E : Type} [Field E] [NumberField E]

theorem continuous_withVal (w : HeightOneSpectrum (𝓞 E)) (f : E →+* Om l)
    (h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1) (y : E) (hy0 : y ≠ 0) (hy : ‖f y‖ < 1) :
    Continuous (f.comp (WithVal.equiv (w.valuation E)).toRingHom) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
  let x0 : WithVal (w.valuation E) := WithVal.toVal _ (y ^ n)
  have hx0' : x0 ≠ 0 := by
    intro h
    exact pow_ne_zero n hy0 ((WithVal.equiv (w.valuation E)).symm.map_eq_zero_iff.1 h)
  have h0 : Valued.v.restrict x0 ≠ 0 := by simp [hx0']
  filter_upwards [Valued.mem_nhds_zero.2 ⟨Units.mk0 _ h0, subset_rfl⟩] with z hz
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
  have hz' : w.valuation E (WithVal.equiv (w.valuation E) z) < w.valuation E (y ^ n) := hz
  have hv : 0 < w.valuation E (y ^ n) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero n hy0))
  have hu : w.valuation E (WithVal.equiv (w.valuation E) z / y ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hv).2 hz'.le
  have h2 := h1 _ hu
  have hp : 0 < ‖f y‖ ^ n := pow_pos (norm_pos_iff.2 ((map_ne_zero f).2 hy0)) n
  rw [map_div₀, map_pow, norm_div, norm_pow, div_le_one₀ hp] at h2
  rw [dist_zero_right]
  exact lt_of_le_of_lt h2 hn

def toKw {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

theorem existsUnique_continuous_induced : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj LL' τ'
  let g : E →+* ↥LL'.1 := (τ' : ↥Bw.Kw.1 →+* ↥LL'.1).comp (toKw Bw)
  let f : E →+* Om l := (algebraMap ↥LL'.1 (Om l)).comp g
  have hfn : ∀ x, ‖f x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => norm_coe_algHom τ' (toKw Bw x)
  have hlt : ∀ y : 𝓞 E, ‖f (y : E)‖ < 1 ↔ y ∈ w.asIdeal := fun y => by
    rw [hfn, ← hj.valuation_lt_one_iff]
    exact hA y
  have hint : ∀ y : 𝓞 E, ‖f (y : E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral (by
      convert map_isIntegral_int f (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hd : 1 ≤ ‖f ((d : 𝓞 E) : E)‖ := not_lt.1 fun hl => d.2 ((hlt _).1 hl)
    have h2 : ‖f x‖ * ‖f ((d : 𝓞 E) : E)‖ = ‖f (n : E)‖ := by
      rw [← norm_mul, ← map_mul]
      exact congrArg (fun z => ‖f z‖) h
    have h3 := hint n
    nlinarith [norm_nonneg (f x)]
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc := continuous_withVal w f h1 (y : E) (by simpa using hy0) ((hlt y).2 hyw)
  have hcg : Continuous (g.comp (WithVal.equiv (w.valuation E)).toRingHom) :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hc
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : CompleteSpace ↥LL'.1 := FiniteDimensional.complete ℚ_[l] ↥LL'.1
  let ext : w.adicCompletion E →+* ↥LL'.1 :=
    (UniformSpace.Completion.extensionHom _ hcg).comp (HeightOneSpectrum.adicCompletion.equiv E w).toRingHom
  have hextc : Continuous ext := UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w)
  have hext : ∀ x : E, ext (algebraMap E _ x) = g x := fun k =>
    UniformSpace.Completion.extensionHom_coe _ hcg (WithVal.toVal _ k)
  have hval : ∀ x : E, ((ext (algebraMap E _ x) : ↥LL'.1) : Om l) = f x := fun x =>
    congrArg (Subtype.val) (hext x)
  refine ⟨⟨(algebraMap ↥LL'.1 (Om l)).comp ext, continuous_subtype_val.comp hextc⟩, fun x => (hval x), ?_⟩
  rintro ⟨j', hj'c⟩ hj'
  refine Subtype.ext (DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hj'c
    (continuous_subtype_val.comp hextc) (funext fun x => ?_)))
  exact (hj' x).trans (hval x).symm

end GlobalTheory.CompanionTheory.EmbUniq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorizationStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_factorization : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → ∀ i ∈ IwU σ n, ∃ u ∈ IwU σ n, IsUnipU u ∧ ∃ y ∈ IwU σ n, t⁻¹ * y * t ∈ IwU σ n ∧ i = u * y := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | exact GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | (intros; apply GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFiniteStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_index_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧ ∀ t : GU σ n, Finite (IwU σ n ⧸ (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | exact GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | (intros; apply GlobalTheory.CompanionTheory.SatPow.finite_index_iwU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecompositionStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_bruhat_decomposition : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n, ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  first | exact @GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | exact GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | (intros; apply GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelConvolution
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem isOpen_GLs_kerconv (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_unitary_mem_GLs_kerconv {n : ℕ} {y : Mat n} (hy : y ∈ GLs n)
    (k₂ : Matrix.unitaryGroup (Fin n) ℂ) : y * k₂.1 ∈ GLs n := by
  have h1 : y.det ≠ 0 := hy
  have h2 : (k₂.1 : Mat n).det ≠ 0 := by
    have h3 : (star k₂.1 * k₂.1 : Mat n) = 1 := Unitary.star_mul_self_of_mem k₂.2
    intro h0
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h4
    exact zero_ne_one h4
  change (y * k₂.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1 h2

theorem act_congr_kerconv {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) {f f' : Mat n → E.V} (h : ∀ x ∈ GLs n, f x = f' x)
    {x : Mat n} (hx : x ∈ GLs n) : act μ E k f x = act μ E k f' x := by
  unfold act
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hy : (y.val).det ≠ 0 := by
    have := y.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hxy : x * y.val ∈ GLs n := by
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  simp only [h _ hxy]

theorem one_mem_GLs_kerconv (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  change (1 : Mat n).det ≠ 0
  simp

theorem conv_eq_of_isKer : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  intro hLg _ hRC hWS hWE hKU n _ _ μ _ E w w' g g' T T' k k' K hg hg' hk hk' hK y hy
  have rk : KReg k := ⟨hk.1.continuousOn, hk.2.1⟩
  have rk' : KReg k' := ⟨hk'.1.continuousOn, hk'.2.1⟩
  have rK : KReg K := ⟨hK.1.continuousOn, hK.2.1⟩
  have rc : KReg (conv μ E k k') := kReg_conv hLg n μ E k k' rk rk'
  have hk'eq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂ := by
    intro y hy k₂
    have := hk'.2.2.1 y hy 1 k₂
    simpa using this
  have hKeq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K (y * k₂.1) = K y * E.ρ k₂ := by
    intro y hy k₂
    have := hK.2.2.1 y hy 1 k₂
    simpa using this
  have hceq := conv_right_equivariant hLg n μ E k k' rk rk' hk'eq
  have key := hKU n μ E (fun y => conv μ E k k' y - K y) (GLs n) (isOpen_GLs_kerconv n) subset_rfl
    (fun y hy k₂ => mul_unitary_mem_GLs_kerconv hy k₂) (rc.1.sub rK.1)
    (fun y hy k₂ => by
      simp only [hceq y hy k₂, hKeq y hy k₂]
      exact (sub_mul _ _ _).symm)
    (fun f hf hc _ => by
      obtain ⟨u, hu, hu0⟩ := hWE n E f hf
      obtain ⟨v, hv, hv0, hvc⟩ := GlobalTheory.T.wave_kernel_composition hRC hWS n E u w w' g g' T T' hu hg hg'
      have h1 := one_mem_GLs_kerconv n
      have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
      have hlin := act_eq_sum_of_kernel hLg n μ E (ι := Bool) (fun b => if b then 1 else -1)
        (fun b => if b then conv μ E k k' else K) (fun y => conv μ E k k' y - K y) f
        (fun b => by cases b <;> simp [rc, rK])
        (fun y _ => by simp [Fintype.sum_bool, sub_eq_add_neg]) hfc 1 h1
      have hc1 : act μ E (conv μ E k k') f 1 = act μ E k (act μ E k' f) 1 :=
        act_conv hLg n μ E k k' f rk rk' hfc 1 h1
      have hact' : ∀ x ∈ GLs n, act μ E k' f x = v 0 x := by
        intro x hx
        rw [act_congr_kerconv μ E k' (fun z hz => (hu0 z hz).symm) hx, hk'.2.2.2 u hu x hx, hv0 x hx]
      have hc2 : act μ E k (act μ E k' f) 1 = act μ E K f 1 := by
        rw [act_congr_kerconv μ E k hact' h1, hk.2.2.2 v hv 1 h1, hvc 1 h1,
          ← hK.2.2.2 u hu 1 h1]
        exact act_congr_kerconv μ E K hu0 h1
      rw [hlin]
      simp [Fintype.sum_bool, hc1, hc2]) y hy
  exact sub_eq_zero.1 key

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WavePairingTimeSymmetryStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_pairing_time_symmetry : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.wave_symm | exact GlobalTheory.CompanionTheory.WaveMult.wave_symm | (intros; apply GlobalTheory.CompanionTheory.WaveMult.wave_symm <;> assumption)
end

