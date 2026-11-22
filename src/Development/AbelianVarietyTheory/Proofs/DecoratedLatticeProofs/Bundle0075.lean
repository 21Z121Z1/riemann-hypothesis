import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfIdeleNegOneNotMemClosurePrincipalIdentityComp
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.RealSignIdele

variable {E : Type} [Field E] [NumberField E]

theorem pos_of_mem_conn {w : InfinitePlace E} (hw : w.IsReal) {u : (InfiniteAdeleRing E)ˣ}
    (hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw ((u : InfiniteAdeleRing E) w) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : Continuous (fun y : w.Completion => e y) :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => e ((u : InfiniteAdeleRing E) w)
  have hg : Continuous g := he.comp ((continuous_apply w).comp Units.continuous_val)
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : (u : InfiniteAdeleRing E) w = 0 := (map_eq_zero e).mp h
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) h1
  have hg1 : g 1 = 1 := map_one e
  by_contra hneg
  obtain ⟨v, -, hv⟩ := isPreconnected_connectedComponent.intermediate_value hu mem_connectedComponent
    hg.continuousOn (show (0 : ℝ) ∈ Set.Icc (g u) (g 1) from ⟨not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  exact hg0 v hv

theorem norm_eq_one_of_sub_one_mem {a : 𝓞 E} (ha : IsUnit a) (h3 : a - 1 ∈ Ideal.span {(3 : 𝓞 E)}) :
    Algebra.norm ℤ a = 1 := by
  classical
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 h3
  have ea : a = 1 + (3 : ℤ) • m := by
    rw [zsmul_eq_mul, Int.cast_ofNat, mul_comm, hm]; ring
  let b := RingOfIntegers.basis E
  have hdet : (Int.castRingHom (ZMod 3)) (Algebra.norm ℤ a) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ea, map_add, map_one, map_zsmul]
    have : (Int.castRingHom (ZMod 3)).mapMatrix (1 + (3 : ℤ) • Algebra.leftMulMatrix b m) = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        map_add, map_mul, eq_intCast, Int.cast_ofNat]
      have h30 : (3 : ZMod 3) = 0 := rfl
      rw [h30, zero_mul, add_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this, Matrix.det_one]
  have hu : IsUnit (Algebra.norm ℤ a) := ha.map _
  rcases Int.isUnit_iff.1 hu with h | h
  · exact h
  · rw [h] at hdet
    exact absurd hdet (by decide)

theorem div_norm_of_pos {r : ℝ} (hr : 0 < r) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact div_self (Complex.ofReal_ne_zero.2 hr.ne')

theorem div_norm_of_neg {r : ℝ} (hr : r < 0) : (r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ) = -1 := by
  rw [Complex.norm_real, Real.norm_of_nonpos hr.le, Complex.ofReal_neg, div_neg,
    div_self (Complex.ofReal_ne_zero.2 hr.ne)]

theorem norm_ne_one_of_sign {w : InfinitePlace E} (hw : w.IsReal) {k : E} (hk : k ≠ 0)
    (hneg : InfinitePlace.embedding_of_isReal hw k < 0)
    (hpos : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), w' ≠ w → 0 < InfinitePlace.embedding_of_isReal hw' k) :
    Algebra.norm ℚ k ≠ 1 := by
  classical
  intro hN
  have cc : ∀ ψ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ := fun ψ => star_star ψ
  let f : (E →+* ℂ) → ℂ := fun φ => φ k / ((‖φ k‖ : ℝ) : ℂ)
  have hprod : ∏ φ : E →+* ℂ, φ k = 1 := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ k
    rw [hN, map_one] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun φ => rfl
  have habs : ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]
  have h1 : ∏ φ : E →+* ℂ, f φ = 1 := by
    simp only [f]
    rw [Finset.prod_div_distrib, hprod, habs, div_one]
  have hnz : ∀ φ : E →+* ℂ, φ k ≠ 0 := fun φ => (map_ne_zero φ).2 hk
  have h2 : ∏ φ ∈ Finset.univ.erase w.embedding, f φ = 1 := by
    refine Finset.prod_involution (fun φ _ => ComplexEmbedding.conjugate φ) (fun φ _ => ?_) (fun φ hφ => ?_)
      (fun φ hφ => ?_) (fun φ _ => cc φ)
    · simp only [f]
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      have hn : ((‖φ k‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hnz φ))
      push_cast
      field_simp
    · intro hf heq
      apply hf
      have hr : ComplexEmbedding.IsReal φ := ComplexEmbedding.isReal_iff.2 heq
      have hemb := InfinitePlace.embedding_mk_eq_of_isReal hr
      have hw' : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_iff.2 (by rw [hemb]; exact hr)
      have hne : InfinitePlace.mk φ ≠ w := by
        rintro h
        apply (Finset.mem_erase.1 hφ).1
        rw [← hemb, h]
      have e1 : φ k = ((InfinitePlace.embedding_of_isReal hw' k : ℝ) : ℂ) := by
        rw [InfinitePlace.embedding_of_isReal_apply, hemb]
      simp only [f]
      rw [e1]
      exact div_norm_of_pos (hpos _ hw' hne)
    · refine Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 hφ).1 ?_, Finset.mem_univ _⟩
      rw [← cc φ, h]
      exact ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
  have h3 : f w.embedding = -1 := by
    simp only [f]
    rw [← InfinitePlace.embedding_of_isReal_apply hw]
    exact div_norm_of_neg hneg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w.embedding), h2, h3, mul_one] at h1
  norm_num at h1

open GlobalTheory.RayFromArtin GlobalTheory.Mem.LocTriv in

theorem infIdele_neg_one_not_mem :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E), w.IsReal →
      ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) ∉ ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  intro E _ _ w hw hx
  let 𝔪 : Ideal (𝓞 E) := Ideal.span {(3 : 𝓞 E)}
  have hm : 𝔪 ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    have h' := congrArg (algebraMap (𝓞 E) E) h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hle : ((diagUnits E).range ⊔ infConn E).topologicalClosure ≤ rayGrp 𝔪 :=
    Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (infConn_le_rayIdl 𝔪) _)
      (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right (isOpen_rayIdl hm)))
  obtain ⟨_, ⟨k, rfl⟩, z, hz, e⟩ := Subgroup.mem_sup.1 (hle hx)
  set x := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) with hxdef
  have hku : diagUnits E k = x * z⁻¹ := eq_mul_inv_of_mul_eq e
  obtain ⟨hunit, hcong, hinf⟩ := inv_mem hz

  have hev : ∀ v, ev v (diagUnits E k : AdeleRing (𝓞 E) E) = ev v ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E) := by
    intro v
    rw [hku, Units.val_mul, map_mul]
    show (x : AdeleRing (𝓞 E) E).2 v * _ = _
    rw [hxdef, infIdele_snd, one_mul]
  have hval : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) = 1 := fun v => by
    rw [← valued_algebraMap, ← ev_diagUnits, hev]
    exact hunit v
  have hcong' : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 → v.valuation E ((k : E) - 1) ≤ rad 𝔪 v :=
    fun v hv => by
      rw [← valued_algebraMap, map_sub, map_one, ← ev_diagUnits, hev]
      exact hcong v hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (k : E) fun v => (hval v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k⁻¹ : Eˣ) : E) fun v => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have hab : a * b = 1 := IsFractionRing.injective (𝓞 E) E (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  have ha1 : a - 1 ∈ 𝔪 := (mem_iff_rad hm _).2 fun v => by
    by_cases hv : v.asIdeal ∣ 𝔪
    · have e1 : ((a - 1 : 𝓞 E) : E) = (k : E) - 1 := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, ha]
      rw [e1]
      exact hcong' v hv
    · rw [rad_eq_one hm hv]
      exact v.valuation_le_one _
  have hN : Algebra.norm ℚ (k : E) = 1 := by
    rw [← ha, ← RingOfIntegers.coe_eq_algebraMap, ← Algebra.coe_norm_int,
      norm_eq_one_of_sub_one_mem ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩ ha1, Int.cast_one]

  have hcomp : ∀ w' : InfinitePlace E, algebraMap E w'.Completion (k : E) =
      (x : AdeleRing (𝓞 E) E).1 w' * ((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w' := fun w' => by
    have := congrArg (fun t : Ideles E => (t : AdeleRing (𝓞 E) E).1 w') hku
    simp only [Units.val_mul, Prod.fst_mul, Pi.mul_apply] at this
    exact this
  have hemb : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal), InfinitePlace.embedding_of_isReal hw' (k : E) =
      InfinitePlace.Completion.ringEquivRealOfIsReal hw' (algebraMap E w'.Completion (k : E)) := fun w' hw' =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw' ((WithAbs.equiv w'.1).symm (k : E))).symm
  have hpos' : ∀ (w' : InfinitePlace E) (hw' : w'.IsReal),
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw' (((z⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).1 w') :=
    fun w' hw' => pos_of_mem_conn hw' hinf
  refine norm_ne_one_of_sign hw (k := (k : E)) k.ne_zero ?_ (fun w' hw' hne => ?_) hN
  · rw [hemb, hcomp, hxdef, infIdele_fst_self, Units.val_neg, Units.val_one, neg_one_mul, map_neg]
    exact neg_neg_of_pos (hpos' w hw)
  · rw [hemb, hcomp, hxdef, infIdele_fst_ne E w w' hne, one_mul]
    exact hpos' w' hw'

end GlobalTheory.RealSignIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeEig

theorem esymm_map_mul_right' (t : ℂ) (M : Multiset ℂ) (j : ℕ) :
    (M.map fun b => b * t).esymm j = t ^ j * M.esymm j := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hc]
  ring

theorem det_torus_indic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (ϖ : kˣ) (s : Finset D) :
    GeneralLinearGroup.det (torusElt k D ϖ (indic s)) = ϖ ^ s.card := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_pow_eq_pow_val]
  simp only [indic]
  simp only [apply_ite (fun n : ℤ => (ϖ : k) ^ n), zpow_one, zpow_zero]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem genVal_shift (q a N : ℕ) (B : Multiset ℂˣ) (u : ℂˣ) (n : ℕ) :
    genVal q a N B n = genVal q 0 N (B.map (· * u⁻¹)) n * ((u : ℂ) ^ n * ((Real.sqrt q : ℝ) : ℂ) ^ (a * n)) := by
  have e : (B.map (· * u⁻¹)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map (fun b : ℂˣ => (b : ℂ))).map (fun z => z * ((u⁻¹ : ℂˣ) : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  simp only [genVal, e, esymm_map_mul_right', zero_mul, zero_add, pow_add, Units.val_inv_eq_inv_val, inv_pow]
  have := u.ne_zero
  field_simp

theorem realKey (a n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 < q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : a = 0 ∨ 0 < Hm) : (c * Real.sqrt Hmg) ^ a = (Real.sqrt q ^ n * Real.sqrt Hm) ^ a ∧ Real.sqrt Hmg ^ a ≠ 0 := by
  rcases h with h0 | hpos
  · simp [h0]
  · have hHmg : 0 < Hmg := by
      by_contra hle
      push_neg at hle
      have h3 : c ^ 2 * Hmg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
      have h4 : 0 < q ^ n * Hm := mul_pos (pow_pos hq0 _) hpos
      linarith
    refine ⟨congrArg (· ^ a) ?_, pow_ne_zero _ (Real.sqrt_pos.2 hHmg).ne'⟩
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hHmg.le, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt hq0.le, hq]

theorem realNeg (n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 ≤ q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : Hm ≤ 0) : Hmg ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have h3 : 0 < c ^ 2 * Hmg := mul_pos (pow_pos hc 2) hlt
  have h4 : q ^ n * Hm ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq0 _) h
  linarith

theorem alg1 (fmg P r ξm ξκ ξn ξκ' C : ℂ) (hr : r ≠ 0) (h1 : ξm ≠ 0) (h2 : ξκ ≠ 0) (h3 : ξn ≠ 0) (h4 : ξκ' ≠ 0)
    (hf : fmg = (ξm * (ξκ * (ξn * ξκ')))⁻¹ * P / r) :
    fmg * (ξn * ξm * (C * r)) = ξκ⁻¹ * (C * (ξκ'⁻¹ * P)) := by
  subst hf
  field_simp

theorem alg2 (S P lam0 ξn ξm Q Sg : ℂ) (h1 : ξn ≠ 0) (h2 : ξm ≠ 0) (h3 : Q ≠ 0) (h4 : Sg ≠ 0)
    (h : S * (ξn * ξm * (Q * Sg)) = lam0 * (ξn * Q) * P) : S = lam0 * (ξm⁻¹ * P / Sg) := by
  have hnq : ξn * Q ≠ 0 := mul_ne_zero h1 h3
  field_simp
  apply mul_left_cancel₀ hnq
  linear_combination h

theorem coeff_isEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ξ hξt hξu V _ _ π B x ℓ hgen hco H hH f hf
  have hbi : IsBiType ξ (fun h => ℓ (π h x)) := by
    intro j hj d hd g
    constructor
    · show ℓ (π (j * g) x) = _
      rw [map_mul, Module.End.mul_apply]
      exact hco j hj d hd _
    · show ℓ (π (g * j) x) = _
      rw [map_mul, Module.End.mul_apply, hgen.1 j hj d hd, map_smul, map_smul, smul_eq_mul]
  have hdet : ∀ κ : GL D k, ((GeneralLinearGroup.det κ : kˣ) : k) = (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ)).1.toBlocks₂₂.det := by
    intro κ
    rw [val_emb_one, toBlocks_fromBlocks₂₂, GeneralLinearGroup.val_det_apply]
  have hφL : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * m)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).1
  have hφR : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m * κ)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).2
  refine ⟨fun κ hκ m => ⟨?_, ?_⟩, fun s R hR m => ?_⟩
  · rw [hf, hf, hφL κ hκ m, (hH.1 κ hκ m).1, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · rw [hf, hf, hφR κ hκ m, (hH.1 κ hκ m).2, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · set w := torusElt k D ϖ (indic s) with hw
    choose! κc hκc κ'c hκ'c hgκ using hR.1
    have hdec : ∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * w * κ' :=
      fun g hg => ⟨_, hκc g hg, _, hκ'c g hg, hgκ g hg⟩
    choose! N hN using fun g hg => GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul k A D ϖ hϖ s g (hdec g hg)
    obtain ⟨R', hrep, hsum⟩ := GlobalTheory.T.lowerUnipotent_diag_doubleCoset_representatives k A D ϖ hϖ s R hR κc κ'c
      (fun g hg => ⟨hκc g hg, hκ'c g hg, hgκ g hg⟩) N hN
    have heig := hgen.2.2 s R' blockDet hrep
    set E := fun m : GL D k => emb₂ k (Equiv.refl (A ⊕ D)) (1, m) with hE
    set φ : GL (A ⊕ D) k → ℂ := fun h => ℓ (π h x) with hφ
    have hφR' : ∀ κ ∈ KO k D, ∀ m, φ (E (m * κ)) = (ξ (GeneralLinearGroup.det κ) : ℂ) * φ (E m) := hφR
    set c : GL D k → ℕ := fun g => (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) with hc
    set lamA := genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card with hlamA
    have e0 : ∀ J, ℓ (π (E m) (π J x)) = φ (E m * J) := fun J => by simp only [hφ, map_mul, Module.End.mul_apply]
    have h1 : lamA * φ (E m) = ∑ j ∈ R', (((ξ (blockDet j))⁻¹ : ℂˣ) : ℂ) * φ (E m * (j * mtor ϖ (indic s))) := by
      have := congrArg (fun v => ℓ (π (E m) v)) heig
      simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [← e0]
      exact this
    have hterm : ∀ g ∈ R, ∑ ν ∈ N g, (((ξ (blockDet (lowU ν * E (κc g))))⁻¹ : ℂˣ) : ℂ) *
        φ (E m * (lowU ν * E (κc g) * mtor ϖ (indic s))) =
        (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      have hcnt := (GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g)
        (hN g hg)).1
      have e1 : ∀ ν : Matrix D A k, E m * (lowU ν * E (κc g) * mtor ϖ (indic s)) = lowU (m.1 * ν) * E (m * κc g * w) := by
        intro ν
        simp only [hE]
        rw [mtor_eq, ← mul_assoc, ← mul_assoc, emb_mul_lowU, mul_assoc (lowU _), emb_mul_emb, mul_assoc (lowU _),
          emb_mul_emb]
      have hb : ∀ (ν : Matrix D A k) (κ : GL D k), blockDet (lowU ν * E κ) = GeneralLinearGroup.det κ :=
        fun ν κ => blockDet_lowU_emb ν κ
      simp only [hb, e1]
      have hs : ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * E y) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧
          (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (E y) else 0 :=
        fun ν y => GlobalTheory.T.parahoricBiTransforming_lowerUnipotent_diag_value k A D ξ hξt hξu φ hbi ν y
      simp only [hs, mul_ite, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcnt]
      rw [hy, hφR' _ (inv_mem (hκ'c g hg))]
      simp only [hc]
      push_cast
      ring
    have hf' : ∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * φ (E m) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A := hf
    have h2 : lamA * φ (E m) = ∑ g ∈ R, (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) :=
      h1.trans ((hsum _).trans (Finset.sum_congr rfl hterm))
    have hqc : ∀ g ∈ R, ((c g : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := fun g hg =>
      GlobalTheory.T.unramifiedHeight_lattice_index_identity k D ϖ hϖ H hH m g s (hdec g hg) (mLat k D) (preLat m.1) (preLat (g⁻¹).1) (fun _ => Iff.rfl)
        (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    have hcpos : ∀ g ∈ R, (0 : ℝ) < c g := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      exact_mod_cast (GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g) (hN g hg)).2
    have hdg : ∀ g ∈ R, (ξ (GeneralLinearGroup.det (m * g)) : ℂ) = ξ (GeneralLinearGroup.det m) *
        (ξ (GeneralLinearGroup.det (κc g)) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det (κ'c g)))) := by
      intro g hg
      conv_lhs => rw [hgκ g hg]
      simp only [hw, map_mul, det_torus_indic, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hlam := genVal_shift (resCard k) (Fintype.card A) (Fintype.card D) B (ξ ϖ) s.card
    have hq0' : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
    by_cases hcase : Fintype.card A = 0 ∨ 0 < H m
    · have hq0 : (0 : ℝ) < resCard k := by
        have : 0 < resCard k := Nat.card_pos
        exact_mod_cast this
      have hσ : ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by
        rcases hcase with h0 | hpos
        · simp [h0]
        · exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne')
      have hQ : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq0).ne')
      have hgU : ∀ g ∈ R, f (m * g) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A)) =
          (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) *
          ((c g : ℂ) ^ Fintype.card A * ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
        intro g hg
        obtain ⟨h6, h7⟩ := realKey (Fintype.card A) s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0
          (hqc g hg) hcase
        have h8 : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A =
            (c g : ℂ) ^ Fintype.card A * ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A := by
          have h9 : Real.sqrt (resCard k) ^ (Fintype.card A * s.card) * Real.sqrt (H m) ^ Fintype.card A =
              (c g : ℝ) ^ Fintype.card A * Real.sqrt (H (m * g)) ^ Fintype.card A := by
            rw [← mul_pow, h6, mul_pow, ← pow_mul, mul_comm s.card]
          exact_mod_cast h9
        have h10 : ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by exact_mod_cast h7
        rw [h8]
        simp only [map_inv, Units.val_inv_eq_inv_val]
        refine alg1 _ _ _ _ _ _ _ _ h10 (ξ _).ne_zero (ξ _).ne_zero (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero ?_
        rw [hf' (m * g), Units.val_inv_eq_inv_val, hdg g hg]
      have hS := Finset.sum_mul R (fun g => f (m * g)) ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A))
      rw [Finset.sum_congr rfl hgU, ← h2, hlamA, hlam] at hS
      rw [hf' m, Units.val_inv_eq_inv_val]
      exact alg2 _ _ _ _ _ _ _ (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero hQ hσ (by rw [hS])
    · push_neg at hcase
      obtain ⟨ha, hle⟩ := hcase
      have hz : ∀ m', H m' ≤ 0 → f m' = 0 := by
        intro m' h
        rw [hf' m', Real.sqrt_eq_zero'.2 h, Complex.ofReal_zero, zero_pow ha, div_zero]
      rw [hz m hle, mul_zero]
      exact Finset.sum_eq_zero fun g hg => hz _ (realNeg s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0'
        (hqc g hg) hle)

end GlobalTheory.LowerHeckeEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NcardYbSetLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosetsS

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (GlobalTheory.CouplingCosets.finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosetsS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindexStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  first | exact @GlobalTheory.TwistRenumber.twist_renumber | exact GlobalTheory.TwistRenumber.twist_renumber | (intros; apply GlobalTheory.TwistRenumber.twist_renumber <;> assumption)
end

