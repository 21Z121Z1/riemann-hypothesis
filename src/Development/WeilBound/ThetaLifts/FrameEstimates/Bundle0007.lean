import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0004
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0003
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0005

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem finiteAdeleIdempotentOfF_mul_self (a : AF F) : e0 F * a = ((0, a.2) : Ainf F × Af F) := Prod.ext (zero_mul a.1) (one_mul a.2)

theorem int_mul {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a * b) := fun v => mul_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a + b) := fun v => add_mem (ha v) (hb v)

theorem int_neg {a : Af F} (ha : Int' a) : Int' (-a) := fun v => neg_mem (ha v)

theorem int_zero : Int' (0 : Af F) := fun _ => zero_mem _

theorem int_sum {ι : Type} (s : Finset ι) {a : ι → Af F} (ha : ∀ i, Int' (a i)) : Int' (∑ i ∈ s, a i) :=
  Finset.sum_induction _ _ (fun _ _ => int_add) int_zero fun i _ => ha i

variable (E) in

theorem exists_lattice (V : Set (AE F E)) (hV : V ∈ 𝓝 (0 : AE F E)) :
    ∃ Λ : AddSubgroup (AE F E), (∀ z ∈ Λ, ∀ z' ∈ Λ, z * z' ∈ Λ) ∧ (Λ : Set (AE F E)) ⊆ V ∧
      ∃ V' ∈ 𝓝 (0 : AE F E), ∀ z ∈ V', e0 F • z = z → z ∈ Λ := by
  classical
  have := ring_AE F E
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hs : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let c : AE F E → Fin (Module.finrank F E) → Af F := fun z i => (b.repr z i).2
  have hc : Continuous c := continuous_pi fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (b.coord i))
  let j : (Fin (Module.finrank F E) → Af F) → AE F E := fun y => ∑ i, (show AF F from ((0, y i) : Ainf F × Af F)) • b i
  have hj : Continuous j := continuous_finsetSum _ fun i _ =>
    (show Continuous fun y : Fin (Module.finrank F E) → Af F => (show AF F from ((0, y i) : Ainf F × Af F)) from
      continuous_const.prodMk (continuous_apply i)).smul continuous_const
  have hj0 : j 0 = 0 := Finset.sum_eq_zero fun i _ => zero_smul (AF F) (b i)
  have hO : {a : Af F | Int' a} ∈ 𝓝 (0 : Af F) := (GlobalTheory.AdLat.OpenLat.isOpen_integral F).mem_nhds int_zero
  have h1 : j ⁻¹' V ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)
  obtain ⟨N₁, hN₁, h₁⟩ := exists_pi _ h1
  have h2 : ∀ᶠ a in 𝓝 (0 : Af F), ∀ i j k, Int' (a * c (b i * b j) k) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      ((continuous_mul_const (c (b i * b j) k)).tendsto' 0 0 (zero_mul _)).eventually hO
  obtain ⟨N₂, hN₂, h₂⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h2
  let Λ : AddSubgroup (AE F E) :=
    { carrier := {z | e0 F • z = z ∧ ∃ a : Fin (Module.finrank F E) → Af F, (∀ i, Int' (a i)) ∧ c z = (N₁ * N₂) • a}
      zero_mem' := ⟨smul_zero _, 0, fun _ => int_zero, by funext i; simp [c]⟩
      add_mem' := fun {x y} hx hy => by
        obtain ⟨h, a, ha, e⟩ := hx
        obtain ⟨h', a', ha', e'⟩ := hy
        refine ⟨by rw [smul_add, h, h'], a + a', fun i => int_add (ha i) (ha' i), ?_⟩
        rw [smul_add, ← e, ← e']
        funext i
        simp only [c, map_add]
        rfl
      neg_mem' := fun {x} hx => by
        obtain ⟨h, a, ha, e⟩ := hx
        refine ⟨by rw [smul_neg, h], -a, fun i => int_neg (ha i), ?_⟩
        rw [smul_neg, ← e]
        funext i
        simp only [c, map_neg]
        rfl }
  refine ⟨Λ, ?_, ?_, ?_⟩
  · rintro z ⟨h, a, ha, e⟩ z' ⟨h', a', ha', e'⟩
    refine ⟨by rw [← smul_mul_assoc, h], fun k => ∑ i, ∑ j, N₂ • (N₁ • (a i * a' j)) * c (b i * b j) k,
      fun k => int_sum _ fun i => int_sum _ fun j => h₂ _ ((int_mul (ha i) (ha' j)).nsmul N₁) i j k, ?_⟩
    funext k
    have e1 : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k := by
      have e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]
        simp only [smul_mul_smul_comm]
      change (RingHom.snd (Ainf F) (Af F) : AF F →+* Af F) (b.repr (z * z') k) = _
      rw [e1]
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      refine (map_sum (RingHom.snd (Ainf F) (Af F)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (RingHom.snd (Ainf F) (Af F)) _ _
    rw [e1, e, e', Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul]
    ring
  · rintro z ⟨h, a, ha, e⟩
    have e1 : j (c z) = z := by
      conv_rhs => rw [← h, ← b.sum_repr z, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, finiteAdeleIdempotentOfF_mul_self]
    rw [← e1, e]
    exact h₁ _ (dvd_mul_right _ _) a ha
  · have hN : ((N₁ * N₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hN₁ hN₂).ne'
    let t : Af F := algebraMap F (Af F) ((N₁ * N₂ : ℕ) : F)⁻¹
    have h3 : ∀ᶠ z in 𝓝 (0 : AE F E), ∀ i, Int' (t * c z i) := eventually_all.2 fun i =>
      ((show Continuous fun z => t * c z i from continuous_const.mul ((continuous_apply i).comp hc)).tendsto' 0 0 (by
        have : c 0 i = 0 := by simp [c]
        rw [this, mul_zero])).eventually hO
    refine ⟨_, h3, fun z hz h => ⟨h, fun i => t * c z i, hz, funext fun i => ?_⟩⟩
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hN,
      map_one, one_mul]

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

def IsFin (u : UA σ J) : Prop := e0 F • (mat u - 1) = mat u - 1

omit [NumberField E] in
theorem IsFin.inv {u : UA σ J} (h : IsFin u) : IsFin u⁻¹ := by
  have e : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1)) := by
    rw [mul_sub, show mat u⁻¹ * mat u = 1 from Units.inv_mul u.1, mul_one, neg_sub]
  unfold IsFin at h ⊢
  rw [e, smul_neg, ← Matrix.mul_smul, h]

theorem pow_near (U : Set (UA σ J)) (hU : U ∈ 𝓝 (1 : UA σ J)) :
    ∀ᶠ u in 𝓝 (1 : UA σ J), IsFin u → ∀ p : ℕ, u ^ p ∈ U := by
  classical
  have := ring_AE F E
  let L : Filter (UA σ J) := ⨅ V ∈ 𝓝 (0 : AE F E), 𝓟 {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V}
  have ent : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E),
      (∀ V ∈ 𝓝 (0 : AE F E), ∀ᶠ h in L, ∀ i j, (f h - 1) i j ∈ V) → Tendsto f L (𝓝 1) := fun f hf => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_
    have hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j :=
      continuous_id.add continuous_const
    rw [mem_map]
    filter_upwards [hf _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))] with h hh
    simpa using hh i j
  have hL : L ≤ 𝓝 1 := by
    have : Tendsto (fun h : UA σ J => h) L (𝓝 1) := by
      refine tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)
      exact (ent mat fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.1)).prodMk_nhds
        ((MulOpposite.continuous_op.tendsto _).comp
          (ent (fun h => mat h⁻¹) fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.2)))
    exact this
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (0 : AE F E),
      {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V} ⊆ U := by
    refine (mem_biInf_of_directed ?_ ⟨_, univ_mem⟩).1 (hL hU)
    intro V hV V' hV'
    exact ⟨V ∩ V', inter_mem hV hV', principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).1, fun i j => (hh.2 i j).1⟩,
      principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).2, fun i j => (hh.2 i j).2⟩⟩
  obtain ⟨Λ, hmul, hΛ, V', hV', hop⟩ := exists_lattice E V hV
  have key : ∀ u : UA σ J, (∀ i j, (mat u - 1) i j ∈ Λ) → ∀ p : ℕ, ∀ i j, (mat (u ^ p) - 1) i j ∈ Λ := by
    intro u hu p
    induction p with
    | zero => intro i j; rw [pow_zero, show mat (1 : UA σ J) = 1 from rfl, sub_self]; exact zero_mem _
    | succ p ih =>
      intro i j
      have e : mat (u ^ (p + 1)) - 1 = (mat (u ^ p) - 1) * (mat u - 1) + (mat (u ^ p) - 1) + (mat u - 1) := by
        rw [pow_succ, show mat (u ^ p * u) = mat (u ^ p) * mat u from rfl]; noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => hmul _ (ih i k) _ (hu k j)) (ih i j)) (hu i j)
  have ent' : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 →
      ∀ᶠ h in 𝓝 (1 : UA σ J), ∀ i j, (f h - 1) i j ∈ V' := fun f hf h1 => by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hc : Continuous fun h => (f h - 1) i j := (hf.sub continuous_const).matrix_elem i j
    exact hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV')
  filter_upwards [ent' mat (Units.continuous_val.comp continuous_subtype_val) rfl,
    ent' (fun h => mat h⁻¹) continuous_mat_inv rfl] with u h1 h2 hu p
  refine hVU ⟨fun i j => hΛ (key u (fun i j => hop _ (h1 i j) (congrFun (congrFun hu i) j)) p i j), fun i j => hΛ ?_⟩
  rw [← inv_pow]
  exact key u⁻¹ (fun i j => hop _ (h2 i j) (congrFun (congrFun hu.inv i) j)) p i j

end levelStructure

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

theorem sq_inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) sq_alg_inj

theorem exists_ratEquiv (hp : IsPair B M χX χW om r s r' s') :
    ∃ e : Matrix (Fin n) (Fin d) E ≃ (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) ((e x).1 i), fun i => algebraMap F (AF F) ((e x).2 i)) := by
  choose y z hyz using hp.good.rat
  have hadd : ∀ a b : Matrix (Fin n) (Fin d) E, incM F (a + b) = incM F a + incM F b := fun a b =>
    Matrix.ext fun i j => map_add (inclR (F := F) (AF F)) _ _
  have hsm : ∀ (c : F) (a : Matrix (Fin n) (Fin d) E), incM F (c • a) = algebraMap F (AF F) c • incM F a := fun c a =>
    Matrix.ext fun i j => by
      change (1 : AF F) ⊗ₜ[F] (c • a i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] a i j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
  let l : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have h := hyz (a + b)
        rw [hadd, map_add, hyz a, hyz b] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_add _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_add _ _ _).symm
      map_smul' := fun c a => by
        have h := hyz (c • a)
        rw [hsm, map_smul, hyz a] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_mul _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_mul _ _ _).symm }
  have hinj : Function.Injective l := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : incM F a = incM F b := M.co.e.injective (by rw [hyz a, hyz b, h1, h2])
    exact Matrix.ext fun i j => sq_inclR_inj (congrFun (congrFun h3 i) j)
  have h2 : Module.finrank F E = 2 := hp.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdim : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨Equiv.ofBijective l ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩, hyz⟩

theorem theta_mul_le (hS : CoefSum) (hE : CoefEq) (hp : IsPair B M χX χW om r s r' s') (μ : Measure (Fin n × Fin d → AF F))
    (hμ : μ.IsAddHaarMeasure) : ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      ‖theta om Φ₁ g h‖ₑ * ‖theta om Φ₂ g h‖ₑ ≤ ENNReal.ofReal c * ∑' x : Matrix (Fin n) (Fin d) E,
        ‖coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ))‖ₑ := by
  obtain ⟨c, hc, h1⟩ := hS F _ B.ψ hp.base.std μ hμ
  obtain ⟨e, he⟩ := exists_ratEquiv hp
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ g h => ?_⟩
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h)
  refine (h1 _ (hs _ h₁) _ (hs _ h₂)).trans (le_of_eq ?_)
  rw [← e.tsum_eq]
  congr 1
  refine tsum_congr fun x => ?_
  rw [← he x, hE F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂ g h]

theorem sq_maj_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) :
    0 ≤ maj τ C N z := by
  unfold maj sz
  split_ifs
  · positivity
  · exact le_rfl

theorem sq_le_of_coef {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {t : ℝ≥0∞} {S : Set (Matrix (Fin n) (Fin d) E)}
    {u : Matrix (Fin n) (Fin d) E → ℂ} {C : Set (Ten F E n d)} {N : ℕ} {g : UA σ X.J} {h : UA σ W.J}
    (h1 : t * t ≤ ENNReal.ofReal c * ∑' x, ‖u x‖ₑ) (h0 : ∀ x ∉ S, u x = 0)
    (h2 : ∀ x, ‖u x‖ ≤ a * a * maj B.emb C N (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ)) :
    t ^ 2 ≤ ENNReal.ofReal (√c * a) ^ 2 * latSum B.emb C N S g h := by
  rw [sq]
  refine h1.trans ?_
  have e : ∑' x, ‖u x‖ₑ = ∑' x : S, ‖u x.1‖ₑ := by
    refine (tsum_subtype_eq_of_support_subset (f := fun x => ‖u x‖ₑ) fun x hx => ?_).symm
    by_contra hn
    exact hx (by simp [h0 x hn])
  rw [e, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_mul hc.le, mul_assoc, latSum]
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), sq]
  exact ENNReal.ofReal_le_ofReal (h2 x.1)

end

theorem sqAll_of' (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqAll := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ N
  refine ⟨NNReal.mk √c (Real.sqrt_nonneg c) • p, C, (continuous_const.mul hpc : Continuous fun f => √c * p f), hC,
    fun f g h => ?_⟩
  have hm : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  exact sq_le_of_coef hc (apply_nonneg p f) (h1 _ hm _ hm g h) (fun x hx => absurd (Set.mem_univ x) hx) fun x => h2 f f _

end PositivityTheory.ThKEst

end
end

