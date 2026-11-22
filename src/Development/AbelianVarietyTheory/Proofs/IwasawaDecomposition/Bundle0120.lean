import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AutomorphicArithmetic.WeightCongruences.ExistsUnitEqRootOfUnityMulConjPhaseOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0005
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstFaithful

theorem exists_idem {LL U D R : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [CommRing R] [IsSemisimpleRing R] (α : R →+* End LL D) (π : R →+* F) (iL : LL → R) (iU : U → R)
    (h1 : ∀ a, α (iL a) = algebraMap LL (End LL D) a) (h2 : ∀ c, α (iU c) = m c)
    (h3 : ∀ a, π (iL a) = algebraMap LL F a) (h4 : ∀ c, π (iU c) = τ c) :
    ∃ e : R, π e = 1 ∧ ∀ x, letterMk m F τ x = 0 → α e x = 0 := by
  let : Algebra R F := π.toAlgebra
  obtain ⟨q, hq⟩ := exists_isCompl (RingHom.ker π)
  have h1q : (1 : R) ∈ RingHom.ker π ⊔ q := by rw [hq.sup_eq_top]; trivial
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 h1q
  have hπe : π e = 1 := by
    have := congrArg π hae
    rwa [map_add, RingHom.mem_ker.1 ha, zero_add, map_one] at this
  have hinj : Function.Injective ((Algebra.linearMap R F) ∘ₗ q.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : (y : R) ∈ RingHom.ker π ⊓ q := ⟨hy, y.2⟩
    rw [hq.inf_eq_bot] at this
    exact Subtype.ext this
  obtain ⟨Λ, hΛ⟩ := IsSemisimpleModule.extension_property _ hinj q.subtype
  have hΛ1 : Λ 1 = e := by
    rw [← hπe]; exact LinearMap.congr_fun hΛ ⟨e, he⟩
  have hΛm : ∀ r f, Λ (π r * f) = r * Λ f := fun r f => Λ.map_smul r f
  let β : F →ₗ[LL] End LL D :=
    { toFun := fun f => α (Λ f)
      map_add' := fun f g => by rw [map_add, map_add]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, ← h3, hΛm, map_mul, h1, ← Algebra.smul_def]; rfl }
  have hβ : ∀ f x, TensorProduct.lift β (f ⊗ₜ x) = α (Λ f) x := fun _ _ => rfl
  have hker : ∀ y ∈ letterKer m F τ, TensorProduct.lift β y = 0 := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => TensorProduct.lift β y = 0) hy ?_ ?_ ?_
    · rintro c _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul, LinearMap.smul_apply,
          LinearMap.id_apply, smul_tmul', hβ, hβ, smul_eq_mul, ← h4, hΛm, mul_comm, map_mul, h2,
          End.mul_apply, sub_self]
      | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
    · exact map_zero _
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  refine ⟨e, hπe, fun x hx => ?_⟩
  rw [letterMk, ← LinearMap.mem_ker, ker_letterQ] at hx
  rw [← hΛ1, ← hβ]
  exact hker _ hx

variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem exists_level_tensor (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
    ∀ f : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), (∀ c : ↥(MaximalUnramifiedExtension l), c ^ m = 1 → f c = c) →
      Algebra.TensorProduct.map f (AlgHom.id ℚ_[l] ↥LL.1) r = r := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, hl.out.not_dvd_one, fun f _ => map_zero _⟩
  | tmul c a =>
    obtain ⟨m, hm, hlm, H⟩ := MemLoc.FrobLaws.exists_level c.2
    refine ⟨m, hm, hlm, fun f hf => ?_⟩
    obtain ⟨g, hg⟩ := MemLoc.FrobLaws.exists_ext f
    have h := H g 1 fun ζ hζ => by
      let z : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
      exact (hg z).trans (congrArg Subtype.val (hf z (Subtype.ext hζ)))
    have h' : f c = c := Subtype.ext ((hg c).symm.trans h)
    rw [Algebra.TensorProduct.map_tmul, h', AlgHom.id_apply]
  | add x y hx hy =>
    obtain ⟨m, hm, hlm, ha⟩ := hx
    obtain ⟨n, hn, hln, hb⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln, fun f H => ?_⟩
    rw [map_add, ha f fun ζ hζ => H ζ (by rw [pow_mul, hζ, one_pow]),
      hb f fun ζ hζ => H ζ (by rw [mul_comm, pow_mul, hζ, one_pow])]

theorem exists_algHom_ker (U R Ω : Type) [Field U] [CommRing R] [Algebra U R] [Module.Finite U R] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] (I : Ideal R) (hI : I ≠ ⊤) : ∃ ψ : R →ₐ[U] Ω, ∀ r ∈ I, ψ r = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let := Ideal.Quotient.field M
  let ψ₀ : (R ⧸ M) →ₐ[U] Ω := IsAlgClosed.lift
  refine ⟨ψ₀.comp (Ideal.Quotient.mkₐ _ M), fun r hr => ?_⟩
  have : Ideal.Quotient.mkₐ U M r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIM hr)
  rw [AlgHom.comp_apply, this, map_zero]

theorem exists_restrict (g : GQ l) : ∃ t : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), ∀ c, (t c : Om l) = g c := by
  have hle : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  exact ⟨((g : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict
    (MaximalUnramifiedExtension l).toSubalgebra (fun x => hle ⟨x, x.2, rfl⟩), fun _ => rfl⟩

theorem exists_extend (f : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ a : ↥LL.1, g a = f a :=
  ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
    fun a => f.liftNormal_commutes (Om l) a⟩

theorem exists_translate (I : Ideal (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1)) (hI : I ≠ ⊤)
    (e : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) (he : Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val e ≠ 0) :
    ∃ (n : ℕ) (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1), r ∉ I ∧
      Algebra.TensorProduct.map (frobUr l ^ n) (AlgHom.id ℚ_[l] ↥LL.1) r = e := by
  have := LL.2
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker ↥(MaximalUnramifiedExtension l) _ (Om l) I hI
  obtain ⟨g, hg'⟩ := exists_extend LL
    ((ψ.restrictScalars ℚ_[l]).comp Algebra.TensorProduct.includeRight)
  have hg : ∀ a : ↥LL.1, g a = ψ (1 ⊗ₜ a) := hg'
  obtain ⟨t, ht⟩ := exists_restrict g
  have key : ∀ r, ψ (Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) r) =
      g (Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      have e1 : t c ⊗ₜ[ℚ_[l]] a = t c • ((1 : ↥(MaximalUnramifiedExtension l)) ⊗ₜ[ℚ_[l]] a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e1, map_smul, ← hg,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact congrArg (· * g a) (ht c)
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨m, hm, hlm, H⟩ := exists_level_tensor LL e
  obtain ⟨n, hn⟩ := MemLoc.FrobLaws.gal_root g⁻¹ hm hlm
  refine ⟨n, Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) e, fun h => he ?_, ?_⟩
  · have h0 := hψ _ h
    rw [key] at h0
    exact g.injective (h0.trans (map_zero g).symm)
  · rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    refine H _ fun c hc => ?_
    have hc' : t c ^ m = 1 := by rw [← map_pow, hc, map_one]
    rw [AlgHom.comp_apply, frobUr_pow_root n _ m hm hlm hc', ← map_pow]
    apply Subtype.ext
    rw [ht]
    have := hn c (congrArg Subtype.val hc)
    rw [SubmonoidClass.coe_pow, ← this, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem exists_action {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (hm : ∀ c : k, m (algebraMap k U c) = algebraMap L _ (algebraMap k L c)) :
    ∃ α : U ⊗[k] L →+* End L D, ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a := by
  let : Module k D := Module.compHom D (algebraMap k L)
  have : IsScalarTower k L D := .of_algebraMap_smul fun _ _ => rfl
  let mU : U →ₐ[k] End L D := { m with commutes' := hm }
  exact ⟨(Algebra.TensorProduct.lift mU (IsScalarTower.toAlgHom k L (End L D))
    fun c a => (Algebra.commutes a (m c)).symm).toRingHom, fun _ _ => rfl⟩

theorem eq_zero_of_translate {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] {m : U →+* End L D} (α : U ⊗[k] L →+* End L D)
    (hα : ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a) (σ : ℕ → U →ₐ[k] U) (φ : ℕ → End L D)
    (hinj : ∀ n, Function.Injective (φ n)) (hφ : ∀ n c, φ n * m c = m (σ n c) * φ n) (e : U ⊗[k] L) (x : D)
    (hx : ∀ n, α e (φ n x) = 0)
    (he : ∀ I : Ideal (U ⊗[k] L), I ≠ ⊤ →
      ∃ n r, r ∉ I ∧ Algebra.TensorProduct.map (σ n) (AlgHom.id k L) r = e) : x = 0 := by
  let I : Ideal (U ⊗[k] L) :=
    { carrier := {r | α r x = 0}
      add_mem' := fun {a b} (ha : α a x = 0) (hb : α b x = 0) => show α (a + b) x = 0 by
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := show α 0 x = 0 by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun a b (hb : α b x = 0) => show α (a * b) x = 0 by
        rw [map_mul, End.mul_apply, hb, map_zero] }
  by_contra h0
  have hI : I ≠ ⊤ := fun h => h0 (by
    have : α 1 x = 0 := (Ideal.eq_top_iff_one I).1 h
    rwa [map_one] at this)
  obtain ⟨n, r, hr, hre⟩ := he I hI
  have semi : ∀ s, φ n * α s = α (Algebra.TensorProduct.map (σ n) (AlgHom.id k L) s) * φ n := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hα, hα, ← mul_assoc, hφ, mul_assoc,
        mul_assoc, Algebra.commutes]
    | add y z hy hz => rw [map_add, map_add, map_add, mul_add, add_mul, hy, hz]
  refine hr (?_ : α r x = 0)
  have h1 := LinearMap.congr_fun (semi r) x
  rw [End.mul_apply, End.mul_apply, hre] at h1
  exact hinj n (h1.trans ((hx n).trans (map_zero _).symm))

theorem isSemisimpleRing_tensor : IsSemisimpleRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := by
  have := LL.2
  have : Algebra.FormallyUnramified ℚ_[l] ↥LL.1 := Algebra.FormallyUnramified.of_isSeparable _ _
  have : IsReduced (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) :=
    Algebra.FormallyUnramified.isReduced_of_field ↥(MaximalUnramifiedExtension l) _
  have : IsArtinianRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := IsArtinianRing.of_finite ↥(MaximalUnramifiedExtension l) _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem eq_zero_of_wdMk_phiD_pow (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (x : ↥(Dpst P ρ))
    (hx : ∀ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) = 0) : x = 0 := by
  have := isSemisimpleRing_tensor LL
  obtain ⟨α, hα⟩ := exists_action (k := ℚ_[l]) (mulD P ρ) fun c =>
    LinearMap.ext fun y => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) =
          algebraMap ↥LL.1 _ (algebraMap ℚ_[l] ↥LL.1 c) :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            Module.algebraMap_end_apply, algebraMap_smul]
      exact LinearMap.congr_fun this y.1)
  let π₀ := Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val
  have hπ₀ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (a : ↥LL.1), π₀ (c ⊗ₜ a) = (c : Om l) * a := fun _ _ => rfl
  let := algC ι LL
  obtain ⟨e, he, hk⟩ := exists_idem (mulD P ρ) ℂ (urC ι) α (ι.toRingHom.comp π₀.toRingHom)
    (fun a => 1 ⊗ₜ a) (fun c => c ⊗ₜ 1) (fun a => (hα 1 a).trans (by rw [map_one, one_mul]))
    (fun c => (hα c 1).trans (by rw [map_one, mul_one]))
    (fun a => congrArg ι ((hπ₀ 1 a).trans (one_mul (a : Om l))))
    (fun c => congrArg ι ((hπ₀ c 1).trans (mul_one (c : Om l))))
  have he0 : π₀ e ≠ 0 := fun h => by
    have h' : ι (π₀ e) = 1 := he
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  refine eq_zero_of_translate α hα (fun n => frobUr l ^ n) (fun n => phiD P ρ ^ n) (fun n => ?_)
    (phiD_pow_mulD P ρ) e x (fun n => hk _ (hx n)) fun I hI => exists_translate LL I hI e he0
  rw [End.coe_pow]
  exact (phiD_injective P ρ).iterate n

end GlobalTheory.PstFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.RatPts

theorem exists_mul_apply_eq_of_mul_apply_eq_one_of_involution {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination hz

theorem fixed_of_two {L : Type} [Field L] (c : L →+* L) (z : L) (k k' : Lˣ)
    (h : z * c (k : L) = k) (h' : z * c (k' : L) = k') :
    c ((k⁻¹ * k' : Lˣ) : L) = ((k⁻¹ * k' : Lˣ) : L) := by
  have h0 : c (k : L) ≠ 0 := (map_ne_zero c).2 k.ne_zero
  have h1 : (k : L) ≠ 0 := k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  field_simp
  linear_combination c (k : L) * h' - c (k' : L) * h

open Classical in

theorem rat_points : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  letI := H.cmStar
  have h90 : ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k := by
    intro z
    refine exists_mul_apply_eq_of_mul_apply_eq_one_of_involution (H.conj : H.E →+* H.E) (fun x => ?_) ?_ (z : H.E) ?_
    · show H.conj (H.conj x) = x
      rw [← hc, ← hc, IsCMField.complexConj_apply_apply]
    · by_contra hn
      push Not at hn
      exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext fun x => (hc x).trans (hn x))
    · show (z : H.E) * H.conj (z : H.E) = 1
      rw [← bridge_star_holds R H]
      exact z.2.2
  have hwd : ∀ (z : H.E) (k k' : (H.E)ˣ), z * H.conj (k : H.E) = k → z * H.conj (k' : H.E) = k' →
      (QuotientGroup.mk (diagUnits H.E k) : DtT H) = QuotientGroup.mk (diagUnits H.E k') := by
    intro z k k' h h'
    have hfix := fixed_of_two (H.conj : H.E →+* H.E) z k k' h h'
    have hF : ((k⁻¹ * k' : (H.E)ˣ) : H.E) ∈ H.F :=
      (IsCMField.complexConj_eq_self_iff H.E _).1 ((hc _).trans hfix)
    have hne : (⟨_, hF⟩ : H.F) ≠ 0 := fun e => (k⁻¹ * k').ne_zero (congrArg Subtype.val e)
    have e : upF H.F (Units.mk0 _ hne) = k⁻¹ * k' := Units.ext rfl
    have := (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.1 (Units.mk0 _ hne)
    rw [e, map_mul, map_inv] at this
    exact QuotientGroup.eq.2 this
  refine ⟨isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants H ?_, h90⟩
  choose s hs using h90
  refine ⟨MonoidHom.mk' (fun z => QuotientGroup.mk (diagUnits H.E (s z))) fun z z' => ?_,
    fun k z h => hwd z k (s z) h (hs z)⟩
  rw [← QuotientGroup.mk_mul, ← map_mul]
  refine hwd ((z * z' : unitary H.E) : H.E) _ _ (hs _) ?_
  rw [Submonoid.coe_mul, Units.val_mul, map_mul, mul_mul_mul_comm, hs, hs]

end GlobalTheory.Mem.RatPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FrameVal

theorem exists_galois_ge (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ M ≤ N := by
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  exact ⟨IntermediateField.normalClosure ℚ M ℂ, inferInstance, {}, IntermediateField.le_normalClosure M⟩

theorem exists_roots (n : ℕ) (hn : 0 < n) :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ ∀ x : ℂ, x ^ n = 1 → x ∈ N := by
  have hfin : {x : ℂ | x ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => ?_
    simpa [Polynomial.mem_nthRoots hn] using hx
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ {x : ℂ | x ^ n = 1}, IntermediateField.finiteDimensional_adjoin fun x hx => ?_,
    fun x hx => IntermediateField.subset_adjoin _ _ hx⟩
  exact IsIntegral.of_pow hn (by rw [show x ^ n = 1 from hx]; exact isIntegral_one)

theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {χ : HChar L} {s : ℝ} {M N : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (hMN : M ≤ N) : χ.ValuesIn s N.val.toRingHom := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hMN y.2⟩, hy⟩

theorem exists_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn 0 M.val.toRingHom := by
  obtain ⟨n, hn, ho⟩ := h
  obtain ⟨N, hN, hr⟩ := exists_roots n hn
  refine ⟨N, hN, fun v _ => ⟨⟨(χ.val v : ℂ), hr _ ?_⟩, by simp [HChar.valTw]⟩⟩
  have h1 : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) ho
  have h2 : χ.val v ^ n = 1 := h1 _
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem exists_of_emb {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x, φ x ∈ M :=
  ⟨φ.toRatAlgHom.fieldRange, (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional, fun x => ⟨x, rfl⟩⟩

open Classical in

theorem frame_values : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : HFrame H e), (∀ j τ, ∃ z : ℤ, e j τ = z) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ (∀ g x, H.emb g x ∈ M) ∧ (∀ j, (C.mu0 j).ValuesIn 0 M.val.toRingHom) ∧ C.eta.ValuesIn (1 / 2) M.val.toRingHom ∧ C.chiPsi.ValuesIn 0 M.val.toRingHom ∧ C.del.ValuesIn 0 M.val.toRingHom ∧ C.del'.ValuesIn 0 M.val.toRingHom ∧ ∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ M := by
  intro R H e C he
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have alg := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (R.Psi) (embPsi H) hcm
  choose Me hMe hMe' using fun φ : H.E →+* ℂ => exists_of_emb φ
  have hmu : ∀ j, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C.mu0 j).ValuesIn 0 M.val.toRingHom := by
    intro j
    obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have := alg (C.mu0 j) n 0 hi fun i => by
      obtain ⟨z, hz⟩ := he j i
      have h1 : (n i : ℚ) = 2 * -e j i := hn i
      rw [hz] at h1
      have h2 : n i = 2 * -z := by exact_mod_cast h1
      exact ⟨-z, by rw [h2]; ring⟩
    simpa using this
  choose Mm hMm hMm' using hmu
  obtain ⟨M1, hM1, hM1'⟩ := alg C.eta (fun _ => 1) 1 C.isEta.inf fun _ => by simp
  obtain ⟨M2, hM2, hM2'⟩ := alg C.chiPsi (fun _ => 2) 0 C.isChi.inf fun _ => by simp
  rw [Int.cast_one] at hM1'
  rw [Int.cast_zero, zero_div] at hM2'
  obtain ⟨M3, hM3, hM3'⟩ := exists_of_order C.isDel.fin
  obtain ⟨M4, hM4, hM4'⟩ := exists_of_order C.isDel'.fin
  choose Mo hMo hMo' using fun k : Fin 2 => exists_roots (Nat.card (ZMod (H.g k))ˣ) Nat.card_pos
  obtain ⟨N, hN, hG, hle⟩ := exists_galois_ge ((⨆ φ, Me φ) ⊔ (⨆ j, Mm j) ⊔ (⨆ k, Mo k) ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4)
  simp only [sup_le_iff, iSup_le_iff] at hle
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hle
  refine ⟨N, hN, hG, fun g x => h1 _ (hMe' _ x), fun j => valuesIn_mono (hMm' j) (h2 j), valuesIn_mono hM1' h4,
    valuesIn_mono hM2' h5, valuesIn_mono hM3' h6, valuesIn_mono hM4' h7, fun k a => h3 k (hMo' k _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

end GlobalTheory.Mem.FrameVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.EtaT

theorem card_above {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) :
    (aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

private theorem card_above_of_prime {R : Ranks} (H : Formalism.BasicNotions.Host R) (l : ℕ) (hp : l.Prime) (hl : l ∣ H.condN)
    (P : HeightOneSpectrum (𝓞 H.E)) (hP : ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal) :
    (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 2 := by
  have : Fact l.Prime := ⟨hp⟩
  have hPp := P.isPrime
  have hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP
  have he := H.der.eta.2.2 l hl P.asIdeal
  change (if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [card_above]
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

private theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (N : ℕ) (hN : N ≠ 0)
    (h : (N : A) ∈ P) : ∃ l : ℕ, l.Prime ∧ l ∣ N ∧ (l : A) ∈ P := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl hN
  | one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨l, h1, h2, h3⟩ := ih (fun h0 => hN (by rw [h0, mul_zero])) h
      exact ⟨l, h1, h2.mul_left _, h3⟩

open Classical in

theorem etaT_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  intro R H
  obtain ⟨c, hc, hcm, hunr, -, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H)
    (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by
      obtain ⟨δ, hδ, hval, hprod⟩ := UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ
      refine ⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩
      · have hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun hm => by
          obtain ⟨l, hl, hlN, hlP⟩ := exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm
          rw [card_above_of_prime H l hl hlN P hlP] at hP
          exact absurd hP (by decide)
        have h0 : ordF P δ = 0 := by simp [ordF, hval P hn]
        rw [h0]
        exact Even.zero
      · simp only [zpow_one]
        exact hprod)
  exact ⟨χ, h1, h2, h3, h4⟩

end GlobalTheory.Mem.EtaT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBoundsStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_ideals_counting_bounds : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 → (∀ X : ℝ, 1 ≤ X → {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite ∧ ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X) ∧ (∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2) ∧ ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤ 3 * Real.log (4 * Ideal.absNorm 𝔮) := by
  first | exact @GlobalTheory.Mem.FewPrimes.few_primes | exact GlobalTheory.Mem.FewPrimes.few_primes | (intros; apply GlobalTheory.Mem.FewPrimes.few_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealReS
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end

