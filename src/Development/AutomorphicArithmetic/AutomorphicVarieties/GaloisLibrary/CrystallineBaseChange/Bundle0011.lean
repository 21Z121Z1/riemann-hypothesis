import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import GroundTheory.AutomorphicForms.GL2Classical.CuspConverse

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolCuspFin
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd

namespace UpperTheory.V.Br.HolomorphicCuspFiniteness

private theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

private theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

end UpperTheory.V.Br.HolomorphicCuspFiniteness

open UpperTheory.V.Br.HolomorphicCuspFiniteness in
theorem UpperTheory.V.Br.holCuspFin : UpperTheory.V.Br.HolCuspFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hlev : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  refine ⟨⟨M, hM1, hlev⟩, ?_⟩
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (Complex.I * k * ∑ v, (θ v : ℂ))) dec
  haveI := cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun _ u => (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ k ∈ KLev F 2 M, TR.finRep F 2 k φ = φ) ∧
      (∀ g : GA F 2, (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ})
  have hφ' : IsHol k c ω φ := hφ.1
  refine ⟨hφ.2, hlev φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (holCap F k c ω hω φ hφ').2⟩
  have := UpperTheory.V.Br.rotEig F φ _ hφ'.wt θ (Unitary.toUnits (rot θ)) rfl (g * TR.infGL F 2 (Unitary.toUnits x))
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelVec
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology

namespace UpperTheory.V.Br

private theorem lv_zero {x : Af ℚ} (h : ∀ n : ℕ, ∃ y ∈ Ohat ℚ, x = (n.factorial : ℕ) * y) : x = 0 := by
  by_contra hx
  have hc : IsCompact (Ohat ℚ : Set (Af ℚ)) := by
    convert GroundTheory.Global.isCompact_integralFiniteAdeles ℚ using 1
    exact Set.ext fun _ => mem_Ohat
  have key : ∀ᶠ d in 𝓝 (0 : Af ℚ), ∀ z ∈ (Ohat ℚ : Set (Af ℚ)), x ≠ d * z :=
    hc.eventually_forall_of_forall_eventually fun z _ =>
      (isOpen_ne_fun continuous_const (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using hx)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  obtain ⟨y, hy, e⟩ := h n
  exact hn y hy e

private theorem lv_KLev {U : Set (GL (Fin 2) (Af ℚ))} (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ KLev ℚ 2 M, g ∈ U := by
  by_contra h
  push Not at h
  have hcl : ∀ n : ℕ, IsClosed ((KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ) := fun n =>
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev n.factorial_pos)).inter hU.isClosed_compl
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => (KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ)
    (fun n => Set.inter_subset_inter_left _ (KLev_le_of_dvd (Nat.factorial_dvd_factorial n.le_succ)))
    (fun n => h _ n.factorial_pos) ((isCompact_KLev (Nat.factorial_pos 0)).inter_right hU.isClosed_compl) hcl
  rw [Set.mem_iInter] at hg
  refine (hg 0).2 ?_
  rwa [show g = 1 from Units.ext (Matrix.ext fun a b => sub_eq_zero.1 (lv_zero fun n => (mem_KLev.1 (hg n).1).2.2 a b))]

private theorem lv_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) {N : ℕ} [NeZero N]
    (δ : G →* ZMod N) (W : Submodule ℂ V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {v : V} (hv : v ∈ W) (h0 : v ≠ 0)
    (hk : ∀ g, δ g = 1 → ρ g v = v) :
    ∃ (χ : DirichletCharacter ℂ N), ∃ w ∈ W, w ≠ 0 ∧ ∀ g, χ (δ g) • ρ g w = w := by
  classical
  let f : ZMod N → V := fun a => if h : ∃ g, δ g = a then ρ h.choose v else 0
  have hf : ∀ g, f (δ g) = ρ g v := fun g => by
    have h : ∃ g', δ g' = δ g := ⟨g, rfl⟩
    have := hk (g⁻¹ * h.choose) (by rw [map_mul, h.choose_spec, ← map_mul, inv_mul_cancel, map_one])
    simp only [f, dif_pos h]
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hm : ∀ g a, ρ g (f a) = f (δ g * a) := fun g a => by
    by_cases h : ∃ g, δ g = a
    · obtain ⟨g', rfl⟩ := h
      rw [← map_mul, hf, hf, map_mul, Module.End.mul_apply]
    · have h' : ¬ ∃ g', δ g' = δ g * a := fun ⟨g', e⟩ => h ⟨g⁻¹ * g', by
        rw [map_mul, e, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩
      simp only [f, dif_neg h, dif_neg h', map_zero]
  have hfW : ∀ a, f a ∈ W := fun a => by
    simp only [f]; split_ifs
    · exact hW _ _ hv
    · exact W.zero_mem
  have hs : ∑ χ : DirichletCharacter ℂ N, ∑ a, χ a • f a ≠ 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, DirichletCharacter.sum_characters_eq, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← map_one δ, hf, map_one]
    exact smul_ne_zero (Nat.cast_ne_zero.2 (Nat.totient_pos.2 (NeZero.pos N)).ne') h0
  obtain ⟨χ, -, hχ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine ⟨χ, _, W.sum_mem fun a _ => W.smul_mem _ (hfW a), hχ, fun g => ?_⟩
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (δ.toHomUnits g).mulLeft _ _ fun a => ?_
  rw [map_smul, hm, smul_smul, ← map_mul]
  rfl

private theorem lv_red {M : ℕ} (hM : 1 ≤ M) : ∃ r : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), r x = d ↔ ∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hi : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have uq : ∀ {x : Af ℚ} {d e : ℤ}, (∃ y ∈ Ohat ℚ, x - d = M * y) → (∃ y ∈ Ohat ℚ, x - e = M * y) → (d : ZMod M) = e := by
    rintro x d e ⟨y, hy, hd⟩ ⟨z, hz, he⟩
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
      rw [map_mul, map_sub, map_intCast, map_intCast]
      linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * hi
    obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨n, ?_⟩
    rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
    exact_mod_cast hn
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d => ⟨fun h => ?_, uq (hf x)⟩⟩
  · simpa using uq (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := uq (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this
  · obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨y, hy, h1⟩ := hf x
    have hn' : (d : Af ℚ) - f x = M * n := by exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hn
    exact ⟨y - n, sub_mem hy (intCast_mem _ _), by linear_combination h1 - hn'⟩

private theorem lv_det {N : ℕ} {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G N) :
    ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) ∈ Ohat ℚ := by
  have h := ((memK N g).1 hg).1
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

private theorem lv_conj {R : Type} [CommRing R] (m : Rˣ) (g : GL (Fin 2) R) :
    (aff m 0 * g * (aff m 0)⁻¹).val = !![g 0 0, m * g 0 1; g 1 0 * (m⁻¹ : Rˣ), g 1 1] := by
  change (aff m 0).val * g.val * (aff m 0).inv = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  rw [mul_right_comm, Units.mul_inv, one_mul]

private theorem lv_int {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M)) (a b : Fin 2) :
    (aff m 0 * g * (aff m 0)⁻¹ : GL (Fin 2) (Af ℚ)) a b ∈ Ohat ℚ := by
  obtain ⟨h, -, ⟨y, hy, e⟩, -⟩ := (memK _ g).1 hg
  revert a b
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨h 0 0, mul_mem (hm ▸ natCast_mem _ M) (h 0 1)⟩,
    Fin.forall_fin_two.2 ⟨?_, h 1 1⟩⟩
  change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) ∈ _
  rw [e, Nat.cast_mul, ← hm, mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  exact mul_mem (hm ▸ natCast_mem _ M) hy

private theorem lv_mem {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M))
    (hd : ∃ y ∈ Ohat ℚ, ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) - (1 : ℤ) = (M * M : ℕ) * y) :
    aff m 0 * g * (aff m 0)⁻¹ ∈ KLev ℚ 2 M := by
  refine mem_KLev.2 ⟨lv_int hm hg, fun a b => ?_, ?_⟩
  · have := lv_int hm (inv_mem hg) a b
    rwa [show aff m 0 * g⁻¹ * (aff m 0)⁻¹ = (aff m 0 * g * (aff m 0)⁻¹)⁻¹ by group] at this
  obtain ⟨h, -, ⟨w, hw, e1⟩, z, hz, e2⟩ := (memK _ g).1 hg
  obtain ⟨y, hy, e3⟩ := hd
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Int.cast_one] at e3
  rw [Nat.cast_mul] at e1 e2 e3
  have hM := natCast_mem (Ohat ℚ) M
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨⟨M * (y - g 0 0 * z + g 0 1 * w),
    mul_mem hM (add_mem (sub_mem hy (mul_mem (h 0 0) hz)) (mul_mem (h 0 1) hw)), ?_⟩, ⟨_, h 0 1, ?_⟩⟩,
    Fin.forall_fin_two.2 ⟨⟨w, hw, ?_⟩, ⟨M * z, mul_mem hM hz, ?_⟩⟩⟩
  · change g 0 0 - 1 = _
    linear_combination e3 - g 0 0 * e2 + g 0 1 * e1
  · change m * g 0 1 - 0 = _
    rw [hm, sub_zero]
  · change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) - 0 = _
    rw [e1, ← hm]
    linear_combination (m : Af ℚ) * w * m.mul_inv
  · change g 1 1 - 1 = _
    rw [e2, mul_assoc]

private noncomputable def lowSub (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) where
  carrier := {φ | IsLow k φ}
  zero_mem' := ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
  add_mem' {a b} ha hb :=
    ⟨fun v => by simp only [map_add]; linear_combination (norm := module) ha.wt v + hb.wt v,
      fun v => by simp only [map_add]; linear_combination (norm := module) ha.low v + hb.low v,
      fun v => by simp only [map_add]; linear_combination (norm := module) ha.one v + hb.one v⟩
  smul_mem' c a ha :=
    ⟨fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.wt v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.low v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.one v⟩

private theorem lv_map {k : ℕ} (T : TR.Sm ℚ 2 →ₗ[ℂ] TR.Sm ℚ 2) (hT : ∀ v i j φ, TR.Eop v i j (T φ) = T (TR.Eop v i j φ))
    {φ : TR.Sm ℚ 2} (h : IsLow k φ) : IsLow k (T φ) :=
  ⟨fun v => by rw [hT, hT, ← map_sub, h.wt, map_smul],
    fun v => by rw [hT, hT, hT, hT, ← map_sub, h.low, map_smul, map_add],
    fun v => by rw [hT, hT, ← map_add, h.one, map_zero]⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.levelVec :
    UpperTheory.V.Br.LevelVec := by
  rintro k π ⟨φ, hφ, h0, hl⟩
  obtain ⟨M, hM, hK⟩ := lv_KLev (π.cusp φ hφ).1.level (by simp)
  have hN : 1 ≤ M * M := Nat.mul_pos hM hM
  haveI : NeZero (M * M) := ⟨by omega⟩
  obtain ⟨m, hm⟩ : IsUnit (M : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  obtain ⟨r, hr⟩ := lv_red hN
  let j : ↥(K1G (M * M)) →* ↥(Ohat ℚ) :=
    { toFun := fun g => ⟨_, lv_det g.2⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one Matrix.GeneralLinearGroup.det))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul Matrix.GeneralLinearGroup.det a.1 b.1)) }
  have hW : ∀ g, ∀ w ∈ π.V ⊓ lowSub k, TR.finRep ℚ 2 g w ∈ π.V ⊓ lowSub k := fun g w hw =>
    ⟨π.stable (.fin g) w hw.1, lv_map _ (fun v a b ψ => LinearMap.congr_fun (TR.lie_rt_fin _ g) ψ) hw.2⟩
  obtain ⟨χ, w, hw, hw0, hχ⟩ := lv_eig ((TR.finRep ℚ 2).comp (K1G (M * M)).subtype) (r.comp j) (π.V ⊓ lowSub k)
    (fun g => hW g.1) (hW (aff m 0)⁻¹ φ ⟨hφ, hl⟩)
    (fun h => h0 (by
      have := congrArg (TR.finRep ℚ 2 (aff m 0)) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this))
    (fun g hg => by
      have h1 : TR.finRep ℚ 2 _ φ = φ := hK _ (lv_mem hm g.2 ((hr (j g) 1).1 (by rw [Int.cast_one]; exact hg)))
      change TR.finRep ℚ 2 g.1 (TR.finRep ℚ 2 _ φ) = _
      conv_rhs => rw [← h1]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← mul_assoc, inv_mul_cancel_left])
  obtain ⟨ν, hν⟩ := dirChar (M * M) hN χ⁻¹
  have he : ∀ v, TR.expo ν v = 0 := fun v => TR.expo_eq_of_exp ν v 0 fun t => by
    rw [zero_mul, Complex.exp_zero]
    exact congrArg Units.val (hν.pos _ fun _ => Real.exp_pos _)
  refine ⟨M * M, χ⁻¹, ν, hN, hν, TR.mulChi 2 ν w, ⟨w, hw.1, rfl⟩, (TR.mulChi 2 ν).map_ne_zero_iff.2 hw0,
    lv_map (TR.mulChi 2 ν).toLinearMap (fun v a b ψ => ?_) hw.2, fun u hu => ?_⟩
  · refine (TR.Eop_mulChi ν v a b ψ).trans ?_
    rw [he, ite_self, zero_smul, add_zero]
    rfl
  · refine (TR.rt_mulChi ν (finGL ℚ 2 u) w).trans (congrArg _ ?_)
    obtain ⟨d, hd⟩ := ratAd.2.1 _ hN _ (lv_det hu)
    have h1 := hν.unit (Matrix.GeneralLinearGroup.det u) ⟨lv_det hu, by rw [← map_inv]; exact lv_det (inv_mem hu)⟩ d hd
    have h2 : chiDet 2 ν (finGL ℚ 2 u) = ν.1 (finId ℚ (Matrix.GeneralLinearGroup.det u)) := congrArg ν.1 (TR.det_finGL u)
    rw [MulChar.inv_apply_eq_inv', ← div_eq_mul_inv] at h1
    rw [h2, eq_of_div_eq_one h1, ← (hr (j ⟨u, hu⟩) d).2 hd]
    exact hχ ⟨u, hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PerZero
section
open Filter Topology Asymptotics Function
open scoped Real

private theorem UpperTheory.V.Br.per_tendsto {g : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (hp : Periodic g h)
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z) (C : ℝ) (m : ℕ)
    (hb : ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ h → ‖g z‖ ≤ C * z.im ^ m) :
    ∃ c, Tendsto g (comap Complex.im atTop) (𝓝 c) := by
  have hb' : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ C * z.im ^ m := by
    intro z hz
    have h1 := hp.sub_int_mul_eq (x := z) ⌊z.re / h⌋
    have h2 := Int.sub_floor_div_mul_nonneg z.re hh
    have h3 := Int.sub_floor_div_mul_lt z.re hh
    have h4 := hb (z - (⌊z.re / h⌋ : ℤ) * (h : ℂ)) (by simpa using hz)
      (by simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
            Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero]
          rw [abs_of_nonneg h2]; exact h3.le)
    rw [h1] at h4
    simpa using h4
  have hev : ∀ A : ℝ, ∀ᶠ z : ℂ in comap Complex.im atTop, A ≤ z.im := fun A =>
    tendsto_comap.eventually (eventually_ge_atTop A)
  have hD := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hp
    ((hev 1).mono fun z hz => hd z (by linarith))
  have hO : Periodic.cuspFunction h g =O[𝓝[≠] 0] fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ) := by
    refine IsBigO.of_bound (|C| * (h / (2 * π)) ^ m) ?_
    filter_upwards [(Periodic.invQParam_tendsto hh).eventually (hev 1), self_mem_nhdsWithin] with q hq hq0
    rw [Periodic.cuspFunction_eq_of_nonzero h g hq0]
    refine (hb' _ hq).trans ((le_abs_self _).trans (le_of_eq ?_))
    have : 0 < h / (2 * π) := by positivity
    rw [Periodic.im_invQParam, abs_mul, abs_pow, abs_mul, neg_div, abs_neg, abs_of_pos this,
      Real.rpow_natCast, Real.norm_eq_abs, abs_pow, abs_abs, mul_pow, mul_assoc]
  have ho : (fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ)) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m : ℝ) (s := -1) (by norm_num)).comp_tendsto
      (tendsto_norm_nhdsNE_zero (E := ℂ))
    refine IsLittleO.of_norm_right ?_
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  have hc : (fun _ : ℂ => Periodic.cuspFunction h g 0) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero (E := ℂ)))
  have hT := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hD
    ((hO.trans_isLittleO ho).sub hc)
  exact ⟨_, by
    simpa only [Function.comp_def, Periodic.eq_cuspFunction hh.ne' hp] using
      hT.comp (Periodic.qParam_tendsto hh)⟩

theorem UpperTheory.V.Br.perZero :
    UpperTheory.V.Br.PerZero := by
  intro f N hN hf hper ⟨C, m, hb⟩ hint
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine GroundTheory.Automorphic.GL2Classical.isZeroAtImInfty_of_integral_vadd_eq_zero hN' hper hf ?_ hint
  obtain ⟨c, hc⟩ := UpperTheory.V.Br.per_tendsto hN'
    (GroundTheory.Automorphic.GL2Classical.periodic_comp_ofComplex_of_vadd hper)
    (fun z hz => (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)) C m
    (fun z hz hr => by
      have h0 : 0 < z.im := by linarith
      have := hb ⟨z, h0⟩ hz hr
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h0] using this)
  have h2 : Tendsto f UpperHalfPlane.atImInfty (𝓝 c) := by
    have := hc.comp (show Tendsto ((↑) : UpperHalfPlane → ℂ) UpperHalfPlane.atImInfty
      (comap Complex.im atTop) from tendsto_comap_iff.2 tendsto_comap)
    simpa [Function.comp_def] using this
  exact h2.isBigO_one ℝ
end

