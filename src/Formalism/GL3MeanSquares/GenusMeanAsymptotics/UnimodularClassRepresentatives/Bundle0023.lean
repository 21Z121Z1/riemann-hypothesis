import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0021
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0006
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0008
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem exists_det_span (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V}
    (hx : ∀ i, x i ∈ Submodule.span (𝓞 K) (Set.range b)) :
    ∃ d : 𝓞 K, algebraMap (𝓞 K) K d = b.det x := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hx j)
  have hrepr : ∀ j i, b.repr (x j) i = algebraMap (𝓞 K) K (c j i) := by
    intro j i
    rw [← hc j]
    simp [← algebraMap_smul K, map_sum, Finsupp.single_apply]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  rw [RingHom.map_det, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, hrepr]

theorem discrIdeal_span {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = gdet h b) :
    discrIdeal h (Submodule.span (𝓞 K) (Set.range b)) = Ideal.span {g₀} := by
  apply le_antisymm
  · refine discrIdeal_le b ?_
    intro x hx z hz
    obtain ⟨d, hd⟩ := exists_det_span b hx
    have hz' : z = conjO K d * g₀ * d := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K d) = star (algebraMap (𝓞 K) K d) := by
        first | rfl | simp [conjO]
      rw [hz, map_mul, map_mul, e1, hd, hg]
    rw [hz', Ideal.mem_span_singleton]
    exact ⟨conjO K d * d, by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    refine mem_discrIdeal b (fun i => Submodule.subset_span (Set.mem_range_self i)) ?_
    rw [Basis.det_self, hg]
    simp

omit [StarRing K] in
theorem absNorm_span_singleton_eq [IsTotallyComplex K] (g₀ : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {g₀}) : ℝ) =
      (∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K g₀)) ^ 2 := by
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := by
    intro w
    have hw : ¬ w.IsReal := by
      rw [InfinitePlace.not_isReal_iff_isComplex]
      exact IsTotallyComplex.isComplex w
    simp [InfinitePlace.mult, hw]
  have hp := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K g₀)
  simp only [hm] at hp
  rw [Ideal.absNorm_span_singleton, ← Finset.prod_pow, hp, Nat.cast_natAbs]
  have h3 := Algebra.coe_norm_int g₀
  rw [← h3]
  norm_cast

theorem normD_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by
  haveI : IsTotallyComplex K := hK.1
  have hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j) := fun i j =>
    Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))
  choose c hc using hint
  have hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b := by
    rw [RingHom.map_det]
    unfold gdet
    congr 1
    ext i j
    simp [hc]
  have hle : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  obtain ⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n :=
    ⟨_, rfl⟩
  rw [hn] at hidx ⊢
  have hN := absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx
  rw [discrIdeal_span b hg] at hN
  have hS := absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det
  rw [hg] at hS
  have hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b) :=
    Finset.prod_nonneg (fun w _ => w.1.nonneg _)
  have key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 =
      (∏ w : InfinitePlace K, w (gdet h b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]
    push_cast
    ring
  unfold normD
  rw [← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem exists_smul_iff (N M : Submodule (𝓞 K) V) :
    (∃ g : Formalism.HermitianLatticesTheory.isom h, g • N = M) ↔ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨⟨g, hg⟩, e⟩

theorem finite_rep (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

theorem finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _

theorem exists_classReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s :=
  (Formalism.ThetaLiftIndependence.classRepsDefinite K V h hs (trace_pos hd) L hL).1

theorem exists_pairReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1 n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)

theorem sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (Prod.fst : Submodule (𝓞 K) V × V → _)
    (fun _ _ => rfl) (pairs h L n) (Formalism.HermitianLatticesTheory.genus h L) (pairs_stable hs L n) (fun p hp => hp.1)
    sX s hsX hsr.1 hX (fun M hM => by simp_rw [exists_smul_iff]; exact hsr.2 M hM)
    (fun M hM => finite_stab_lat hs hd hM.1)
  rw [key]
  refine Finset.sum_congr rfl fun M hM => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L n ∧ p.1 = M} = repCount h M n :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.2, (congrArg (fun N : Submodule (𝓞 K) V => p.1.2 ∈ N) p.2.2).mp p.2.1.2.1, p.2.1.2.2⟩
        invFun := fun x => ⟨(M, x.1), ⟨hsr.1 M hM, x.2.1, x.2.2⟩, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.symm rfl)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabLatEquiv M)]

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinrankRingOfIntegers
section
open NumberField Module IsDedekindDomain Function

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def maxEquiv (F : Type) [Field F] [NumberField F] :
    {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} ≃ HeightOneSpectrum (𝓞 F) where
  toFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, idealPowerSpanBounds.ne_bot 𝔭.2⟩
  invFun v := ⟨v.asIdeal, v.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sSup_le_pow (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    sSup {e : ℕ | I ≤ v.asIdeal ^ e} = multiplicity v.asIdeal I := by
  have hfin : FiniteMultiplicity v.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hI
  have : {e : ℕ | I ≤ v.asIdeal ^ e} = Set.Iic (multiplicity v.asIdeal I) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← Ideal.dvd_iff_le, hfin.pow_dvd_iff_le_multiplicity]
  rw [this, csSup_Iic]

theorem absNorm_eq_tprod {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ sSup {e : ℕ | I ≤ 𝔭.1 ^ e} := by
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hφ : ∀ J, φ J = (Ideal.absNorm J : ℝ) := fun _ => rfl
  have h0 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I :=
    Ideal.hasFiniteMulSupport hI
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    exact map_finprod φ h0
  have h2 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => φ (v.maxPowDividing I) :=
    h0.fun_comp (map_one φ)
  have h3 : ∏' v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := tprod_eq_finprod h2
  rw [← hφ, h1, ← h3, ← (maxEquiv F).tprod_eq]
  refine tprod_congr fun 𝔭 => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, hφ,
    ← sSup_le_pow _ hI]
  rfl

theorem finrank_ringOfIntegers (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    finrank (𝓞 F) (𝓞 K) = 2 := by
  rw [← MeanB.finrank_eq_two hK hF]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

theorem absNorm_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers hK hF]

theorem map_le_extP_pow (I 𝔭 : Ideal (𝓞 F)) (e : ℕ) :
    I.map (algebraMap (𝓞 F) (𝓞 K)) ≤ extP K 𝔭 ^ e ↔ I ≤ 𝔭 ^ e := by
  rw [Ideal.map_le_iff_le_comap, MeanB.comap_extP_pow]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def discrF (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) : Ideal (𝓞 F) :=
  (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K))

theorem discrIdeal_eq_map (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) :
    discrIdeal h L = (discrF F h L).map (algebraMap (𝓞 F) (𝓞 K)) := by
  apply le_antisymm
  · conv_lhs => unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    rw [← ht]
    apply Ideal.mem_map_of_mem
    rw [discrF, Ideal.mem_comap, ht]
    exact Ideal.subset_span ⟨x, hx, hz⟩
  · exact Ideal.map_comap_le

theorem vd_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    vd h L 𝔭 = sSup {e : ℕ | discrF F h L ≤ 𝔭 ^ e} := by
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [discrIdeal_eq_map hF hs, map_le_extP_pow]

theorem normD_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (L : Submodule (𝓞 K) V) : normD h L = (Ideal.absNorm (discrF F h L) : ℝ) := by
  unfold normD
  rw [discrIdeal_eq_map hF hs, absNorm_map hK hF, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]

theorem discrIdeal_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g A) = discrIdeal h A := by
  unfold discrIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g.symm (x i), fun i => ?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hx i)
      have : g y = x i := hyx
      change g.symm (x i) ∈ A
      rw [← this, LinearEquiv.symm_apply_apply]
      exact hy
    · rw [e]
      congr 1
      ext i j
      have := hg (g.symm (x i)) (g.symm (x j))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact this
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g (x i), fun i => Submodule.mem_map.mpr ⟨x i, hx i, rfl⟩, ?_⟩
    rw [e]
    congr 1
    ext i j
    exact (hg (x i) (x j)).symm

theorem form_mem_locF (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : h x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨x', hx', ex⟩ := Submodule.mem_map.mp hx
  obtain ⟨y', hy', ey⟩ := Submodule.mem_map.mp hy
  have ex' : g x' = x := ex
  have ey' : g y' = y := ey
  obtain ⟨s, hs, hsx⟩ := (LocF.mem_locF_iff hp L x').mp hx'
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp L y').mp hy'
  rw [← ex', ← ey', hg x' y', LocF.mem_locF_iff hp]
  refine ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  have := hLi _ hsx _ hty
  rw [localizedQuotients.form_smul hF] at this
  rwa [Algebra.smul_def]

end Formalism.HermitianLattices.Ext.L3.BrA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MapMkConjTranspose
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

def isoCount (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) : ℕ :=
  Nat.card {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    Xᴴ * g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))}

theorem map_mk_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) :
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = gᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rfl

theorem isUnit_mk {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) δ) := by
  have h2 : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := Ideal.sup_pow_eq_top hδ
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := h2
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hq : Ideal.Quotient.mk (extP K 𝔭 ^ N) (δ * a) = Ideal.Quotient.mk (extP K 𝔭 ^ N) 1 := by
    rw [Ideal.Quotient.eq]
    have hza : δ * a - 1 = -z := by
      rw [← hyz]
      ring
    rw [hza]
    exact neg_mem hz
  rw [map_mul, map_one] at hq
  exact isUnit_iff_exists_inv.mpr ⟨_, hq⟩

theorem isoCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) {k : ℕ} (hk : 1 ≤ k) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (m ^ 2) * isoCount 𝔭 k g := by
  have hF := hFF.out
  have := finite_quot (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ (k + 1)
  have he' : (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ -
      star (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ)) * Ideal.Quotient.mk _ e = 1 := by
    rw [star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))]
    exact Ideal.Quotient.eq.2 he
  have h := FirstPropositionFrame.card_lift_unimod' (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k)
    (by
      intro a ha b hb
      rw [ker_piQ] at ha hb
      exact mul_eq_zero_idQ (by omega) ha hb) he'
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1))))
    (by rw [map_mk_conjTranspose, hg])
    (by
      have : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).det =
          Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) g.det := (RingHom.map_det _ g).symm
      rw [this]
      exact isUnit_mk hdet _)
    (Ideal.absNorm 𝔭) (card_ker_piQ hK hF h𝔭 k)
  rw [Fintype.card_fin] at h
  have hm : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).map (piQ K 𝔭 k) =
      g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    ext i j
    rfl
  rw [hm] at h
  exact h

theorem isoCount_eq_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (k * m ^ 2) * isoCount 𝔭 1 g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [isoCount_succ hK h𝔭 g hg hdet (by omega), ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

