import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedTheta

variable {l : ℕ} [Fact l.Prime]

open Classical in

def thetaExt (x : Per.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x then Per.θD l h.choose else 0

theorem thetaExt_alg (y : Per.BdRp l) :
    thetaExt (algebraMap (Per.BdRp l) (Per.BdR l) y) = Per.θD l y := by
  have h : ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z =
      algebraMap (Per.BdRp l) (Per.BdR l) y := ⟨y, rfl⟩
  rw [thetaExt, dif_pos h, (BdRField.bdR_isField l).2.1 h.choose_spec]

theorem exists_of_mem_FilD_zero {x : Per.BdR l} (hx : x ∈ Per.FilD l 0) :
    ∃ y : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨e, he⟩ := FilLaws.exists_isEps l
  obtain ⟨y, hy⟩ := (mem_FilD_iff_xi_pow l e he 0 x).1 hx
  exact ⟨y, by simpa using hy⟩

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (c : ℂ_[l]) :
    AI.actC g c = Per.σC g c := by
  have h1 : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  have h2 : Continuous (Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction c using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem norm_untilt_sub (x : Per.Fl l) (y : Per.OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    ‖((x.untilt : Per.OC l) : ℂ_[l]) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h
  have h1 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
  rw [pow_one] at h1
  exact h1

theorem nonempty_thetaL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  intro l _ P AI T
  have hex : ∀ x ∈ (P.PD (MainNotions.LocalSituation.botExt l)).Fil 0,
      ∃ y : Per.BdRp l, T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun x hx => exists_of_mem_FilD_zero ((T.fil _ _ _).1 hx)
  have hU := TiedUnif.tied_uniformiser l P AI T
  refine ⟨{
    θ := fun x => thetaExt (T.eD x)
    θ_one := ?_
    θ_add := fun x hx y hy => ?_
    θ_mul := fun x hx y hy => ?_
    θ_onto := fun c => ?_
    θ_ker := fun x hx => ?_
    θ_act := fun g x hx => ?_
    θ_Om := fun x => ?_
    θ_int := fun a => ?_
    θ_teich := fun x y h => ?_
    fil_succ_iff_mul_t := hU.2.2 _
    t_μ := hU.1 _ }⟩
  · rw [map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), thetaExt_alg, map_one]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_add, hu, hv, ← map_add, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
  · obtain ⟨y, rfl⟩ := (thetaD_props l).1 c
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y), ?_, ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact TiedUnif.alg_mem_FilD_zero y
    · rw [RingEquiv.apply_symm_apply, thetaExt_alg]
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.fil, hu, thetaExt_alg, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.actD, hu, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, thetaExt_alg, thetaExt_alg,
      (thetaD_props l).2.2.2.2, actC_eq]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    rw [hy, thetaExt_alg, hθ]
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1,
      WittVector.fontaineTheta_teichmuller]
    exact norm_untilt_sub x y h

end GlobalTheory.MemLoc.TiedTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Chr.DetOrd

variable {L : Type} [Field L] [NumberField L]

theorem ordF_mul' (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) : ordF w (a * b) = ordF w a + ordF w b := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul ha hb]
  ring

theorem ordF_nonneg_of_isInteger (w : HeightOneSpectrum (𝓞 L)) (a : Lˣ)
    (h : IsLocalization.IsInteger (𝓞 L) (a : L)) : 0 ≤ ordF w a := by
  obtain ⟨r, hr⟩ := h
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hle : w.valuation L (a : L) ≤ 1 := by
    rw [← hr]; exact w.valuation_le_one r
  have := (WithZero.log_le_log ha one_ne_zero).2 hle
  unfold ordF
  simpa using this

theorem ordF_finite (a : Lˣ) : {w : HeightOneSpectrum (𝓞 L) | ordF w a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  apply hw
  have h0 : w.valuation L (a : L) ≠ 0 := by simp
  have h1 : w.valuation L (a : L) = 1 := by
    refine le_antisymm hn.1 ?_
    have h2 := hn.2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 h2
  simp [ordF, h1]

theorem isFractional_detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : M.FG) :
    IsFractional (𝓞 L)⁰ (detSub M) := by
  obtain ⟨a, ha, hint⟩ := Formalism.L2.LamCM.A2.exists_den M hM
  refine ⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem exists_bound {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) :
    ∃ d : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ∀ k : Lˣ, (k : L) ∈ A → -ordF w d ≤ ordF w k := by
  obtain ⟨a, ha, hint⟩ := h
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero ha
  refine ⟨Units.mk0 _ ha0, fun w k hk => ?_⟩
  have h1 := ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by
    have := hint _ hk
    rwa [Algebra.smul_def] at this)
  rw [ordF_mul'] at h1
  linarith

theorem isLeast_ordSub {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    IsLeast {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} (ordSub w A) := by
  obtain ⟨d, hd⟩ := exists_bound h
  have hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} :=
    ⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩
  exact ⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩

theorem ordSub_finite {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A) :
    {w : HeightOneSpectrum (𝓞 L) | ordSub w A ≠ 0}.Finite := by
  obtain ⟨d, hd⟩ := exists_bound h
  refine ((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  apply hw
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  have h1 := hl ⟨k0, hk0, rfl⟩
  have h2 := hd w k hk
  omega

theorem det_of_mulVec {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (x : Fin N → Fin N → L) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem detSub_map {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (M : Submodule (𝓞 L) (Fin N → L)) :
    detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L))) =
      (detSub M).map (LinearMap.mulLeft (𝓞 L) γ.det) := by
  unfold detSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx e using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    have : y = fun i => γ.mulVec (x i) := funext fun i => by
      rw [← e i]; simp
    rw [this, det_of_mulVec]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩
    rw [det_of_mulVec]
    rfl

theorem ordSub_map_mul {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (u : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A.map (LinearMap.mulLeft (𝓞 L) (u : L))) = ordF w u + ordSub w A := by
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩
  rintro n ⟨k', hk', rfl⟩
  obtain ⟨y, hy, ey⟩ := Submodule.mem_map.1 hk'
  have ey' : (u : L) * y = k' := ey
  have hy' : ((u⁻¹ * k' : Lˣ) : L) = y := by
    rw [Units.val_mul, ← ey', Units.inv_mul_cancel_left]
  have h1 := hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩
  have h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k') := by
    rw [← ordF_mul', mul_inv_cancel_left]
  omega

end GlobalTheory.Mem.Chr.DetOrd

namespace GlobalTheory.Mem.Chr

open DetOrd

open Classical in

theorem ordSub_detSub_lattice :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Submodule (𝓞 L) (Fin N → L)), M.FG → Submodule.span L (M : Set (Fin N → L)) = ⊤ → {w | ordSub w (detSub M) ≠ 0}.Finite ∧ (∀ w, IsLeast {n | ∃ k : Lˣ, (k : L) ∈ detSub M ∧ ordF w k = n} (ordSub w (detSub M))) ∧ ∀ (γ : Matrix (Fin N) (Fin N) L) (u : Lˣ), γ.det = u → ∀ w, ordSub w (detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L)))) = ordF w u + ordSub w (detSub M) := by
  intro L _ _ N M hfg hsp
  have hf := isFractional_detSub M hfg
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hsp
  have hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M := det_mem_detSub x hx
  refine ⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩
  have e := detSub_map γ M
  have hu' : γ.det = u := by convert hu
  rw [hu'] at e
  have := ordSub_map_mul hf _ hk u w
  rw [← e] at this
  convert this

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General

open Classical in

theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.UnitOpen

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_val_le (v : HeightOneSpectrum (𝓞 L)) (m : ℤ) :
    IsOpen {x : v.adicCompletion L | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective L (WithZero.exp (-m))
  have h : IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := Valued.isOpen_valuationSubring _
  convert h.preimage (continuous_mul_const p) using 1
  ext x
  show _ ↔ Valued.v (x * p) ≤ 1
  rw [map_mul, hp, WithZero.exp_neg, mul_inv_le_iff₀ (WithZero.exp_pos), one_mul]
  rfl

theorem continuous_comp (v : HeightOneSpectrum (𝓞 L)) :
    Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 v :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)

theorem isOpen_unitIdl : IsOpen (unitIdl L : Set (Ideles L)) := by
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 L) L | ∀ v, a v ∈ v.adicCompletionIntegers L} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have c1 : Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 := continuous_snd.comp Units.continuous_val
  have c2 : Continuous fun a : Ideles L => ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hV.preimage c1).inter (hV.preimage c2) using 1
  ext a
  constructor
  · intro ha
    exact ⟨fun v => (ha v).le, fun v => ((unitIdl L).inv_mem ha v).le⟩
  · rintro ⟨h1, h2⟩ v
    have h : (a : AdeleRing (𝓞 L) L).2 v * ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 L) L => z.2 v) a.mul_inv
    have h3 := congrArg (Valued.v : Valuation (v.adicCompletion L) _) h
    rw [map_mul, map_one] at h3
    have k1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have k2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm k1 ?_
    rw [← h3]
    exact mul_le_of_le_one_right' k2

open Classical in

theorem unit_open_and_congr_open : ∀ (L : Type) [Field L] [NumberField L], IsOpen (unitIdl L : Set (Ideles L)) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), IsOpen {a : Ideles L | a ∈ unitIdl L ∧ ∀ v ∈ S, Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))} := by
  intro L _ _
  refine ⟨isOpen_unitIdl, fun S n => ?_⟩
  have h : IsOpen (⋂ v ∈ S, {a : Ideles L | Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))}) :=
    isOpen_biInter_finset fun v _ => (isOpen_val_le v _).preimage ((continuous_comp v).sub continuous_const)
  convert isOpen_unitIdl.inter h using 1
  ext a
  simp

end GlobalTheory.Mem.UnitOpen
end

