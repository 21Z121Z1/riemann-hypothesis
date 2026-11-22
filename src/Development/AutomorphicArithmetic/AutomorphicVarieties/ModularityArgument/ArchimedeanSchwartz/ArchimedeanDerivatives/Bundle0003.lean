import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.CharSep
section
noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
open IsDedekindDomain Neutral.B1 GlobalTheory.ModelChar GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Z.Inf.H.Phase

private def ex (r : ℝ) : ℂˣ := Circle.toUnits (Circle.exp r)

private theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp [ex, Circle.exp_add]

private theorem ex_zero : ex 0 = 1 := by simp [ex]

variable {K : Type} [Field K] [NumberField K]

private def modU (t : ℝ) : ℂˣ →* ℂˣ where
  toFun z := ex (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp [ex_zero]
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      ex_add]

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

variable (K) in

private def cmp (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  (Units.map (Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toRingHom.toMonoidHom).comp
    (Units.map (infEv w))

variable (K) in

private def ar (n : InfinitePlace K → ℤ) : Ideles K →* ℂˣ where
  toFun a := ∏ w, argU (cmp K w a) ^ n w
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow, Finset.prod_mul_distrib]

variable (K) in

private def md (t : InfinitePlace K → ℝ) : Ideles K →* ℂˣ where
  toFun a := ∏ w, modU (t w) (cmp K w a)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

end UpperTheory.V.Z.Inf.H.Phase

namespace UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf.H.Phase

end UpperTheory.V.Z.Inf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.EventuallyUnr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Inf

namespace InfinitesimalCharacterOf

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem one_le_term (v : HeightOneSpectrum (𝓞 M)) :
    1 ≤ (v.under (𝓞 K)).asIdeal.ramificationIdx' v.asIdeal * (v.under (𝓞 K)).asIdeal.inertiaDeg' v.asIdeal := by
  haveI := v.isMaximal
  haveI : v.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal := ⟨rfl⟩
  haveI := (v.under (𝓞 K)).isMaximal
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal (v.under (𝓞 K)).ne_bot)
    (Ideal.inertiaDeg'_pos (p := (v.under (𝓞 K)).asIdeal) (P := v.asIdeal)).ne')

private theorem normV_split (h2 : Module.finrank K M = 2) {w w' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 K) = w.under (𝓞 K)) : normV w = normV (w.under (𝓞 K)) ^ 1 := by
  classical
  have hww : w'.asIdeal ≠ w.asIdeal := fun e => hne (HeightOneSpectrum.ext e)
  have a := one_le_term (K := K) w
  have b := one_le_term (K := K) w'
  rw [hu] at b
  generalize hp : w.under (𝓞 K) = p at a b hu ⊢
  haveI := p.isMaximal
  have mem : ∀ v : HeightOneSpectrum (𝓞 M), v.under (𝓞 K) = p →
      v.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 M) := by
    rintro v rfl
    rw [IsDedekindDomain.mem_primesOverFinset_iff (v.under (𝓞 K)).ne_bot]
    exact ⟨v.isPrime, ⟨rfl⟩⟩
  have hsub : ({w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 M))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 M) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact mem _ hu
    · exact mem _ hp
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub
  rw [Ideal.sum_ramification_inertia (𝓞 M) K M p.ne_bot, h2, Finset.sum_pair hww] at hle
  have he : p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal = 1 := by omega
  have hf : p.asIdeal.inertiaDeg' w.asIdeal = 1 := Nat.dvd_one.1 (Dvd.intro_left _ he)
  haveI : w.asIdeal.LiesOver p.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hp.symm⟩
  have hN := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot
  rw [hf] at hN
  exact hN

private theorem eventually_unr (χ : HChar K) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, χ.UnrAt (w.under (𝓞 K)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

private theorem unr_pow {L : Type} [Field L] [NumberField L] {μ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := fun x hx => by
  have e : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
  rw [e, h x hx, one_pow]

private theorem val_pow {L : Type} [Field L] [NumberField L] (μ : HChar L) (w : HeightOneSpectrum (𝓞 L)) (k : ℕ) :
    (μ ^ k).val w = μ.val w ^ k := MonoidHom.pow_apply μ.1 k _

private theorem indSys_twist [IsTotallyComplex K] [IsTotallyComplex M] (h2 : Module.finrank K M = 2)
    {P : CuspSub K (2 * 2)} {π : CuspSub M 2} (hI : IndSys (CG.mk π).HasSat (CG.mk P).HasSat) (χ : HChar K) (ξ : HChar M)
    (hξ : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), χ.UnrAt (w.under (𝓞 K)) → normV w = normV (w.under (𝓞 K)) ^ f →
      ξ.UnrAt w ∧ ξ.val w = χ.val (w.under (𝓞 K)) ^ f) (k : ℕ) :
    IndSys (CG.mk (π.twist (ξ ^ k))).HasSat (CG.mk (P.twist (χ ^ k))).HasSat := by
  refine (Filter.Eventually.and hI (eventually_unr (M := M) χ)).mono ?_
  rintro w ⟨⟨h1, h3⟩, hu⟩
  simp only [← CG.twist_mk]
  refine ⟨fun w' hne hw' => ?_, fun hq => ?_⟩
  · obtain ⟨B, B', hB, hB', hBP⟩ := h1 w' hne hw'
    obtain ⟨u1, v1⟩ := hξ w 1 hu (normV_split h2 hne hw')
    obtain ⟨u2, v2⟩ := hξ w' 1 (hw' ▸ hu) (normV_split h2 hne.symm hw'.symm)
    refine ⟨_, _, hB.twist (unr_pow u1 k), hB'.twist (unr_pow u2 k), ?_⟩
    have hP := hBP.twist (unr_pow hu k)
    rw [Multiset.map_add] at hP
    rw [val_pow, val_pow, v1, v2, hw', pow_one]
    rwa [val_pow] at hP
  · obtain ⟨B, B', hB, rfl, hBP⟩ := h3 hq
    obtain ⟨u1, v1⟩ := hξ w 2 hu hq
    have e : (ξ ^ k).val w = ((χ ^ k).val (w.under (𝓞 K))) ^ 2 := by
      rw [val_pow, v1, val_pow, ← pow_mul, ← pow_mul, mul_comm]
    refine ⟨_, B'.map (· * (χ ^ k).val (w.under (𝓞 K))), ?_, rfl, ?_⟩
    · have h := hB.twist (unr_pow u1 k)
      rw [e, Multiset.map_map] at h
      rw [Multiset.map_map]
      convert h using 2
      simp [mul_pow]
    · have h := hBP.twist (unr_pow hu k)
      simpa [Multiset.map_add, Multiset.map_map, Function.comp_def] using h

private theorem over_two (h2 : Module.finrank K M = 2) {τ τ' σ : M →+* ℂ} (hne : τ ≠ τ')
    (h1 : τ'.comp (algebraMap K M) = τ.comp (algebraMap K M)) (h3 : σ.comp (algebraMap K M) = τ.comp (algebraMap K M)) :
    σ = τ ∨ σ = τ' := by
  classical
  letI : Algebra K ℂ := (τ.comp (algebraMap K M)).toAlgebra
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos (by omega)
  let a : ∀ ρ : M →+* ℂ, ρ.comp (algebraMap K M) = τ.comp (algebraMap K M) → (M →ₐ[K] ℂ) :=
    fun ρ h => { ρ with commutes' := fun x => RingHom.congr_fun h x }
  have ha : ∀ ρ h ρ' h', a ρ h = a ρ' h' → ρ = ρ' := fun ρ h ρ' h' e =>
    RingHom.ext fun x => DFunLike.congr_fun e x
  have hc := AlgHom.card K M ℂ
  rw [h2] at hc
  by_contra hcon
  push_neg at hcon
  have h3' : ({a σ h3, a τ rfl, a τ' h1} : Finset (M →ₐ[K] ℂ)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a σ h3, a τ rfl, a τ' h1, fun e => hcon.1 (ha _ h3 _ rfl e), fun e => hcon.2 (ha _ h3 _ h1 e),
      fun e => hne (ha _ rfl _ h1 e), rfl⟩
  have := Finset.card_le_univ ({a σ h3, a τ rfl, a τ' h1} : Finset (M →ₐ[K] ℂ))
  omega

private theorem map_sum' {ι : Type} (s : Finset ι) (f : ℂ → ℂ) (g : ι → Multiset ℂ) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := map_sum (Multiset.mapAddMonoidHom f) g s

end InfinitesimalCharacterOf

open InfinitesimalCharacterOf in
theorem infOf : InfOf := by
  intro hSep hUnion hCS hNC K M _ _ _ _ _ _ _ h2 P π hI τ τ' m m' hne hres hm hm'
  classical
  obtain ⟨χ, hχ⟩ := hCS K
  obtain ⟨ξ, hξe, hξv⟩ := hNC K M χ
  have hex : ∀ φ, ∃ μ, P.HasInfChar φ μ := fun φ => (GlobalTheory.ResW.IrrInfChar.main K (2 * 2) φ).1 P
  choose mP hmP using hex
  have hex' : ∀ σ : M →+* ℂ, ∃ μ, π.HasInfChar σ μ := fun σ => (GlobalTheory.ResW.IrrInfChar.main M 2 σ).1 π
  choose m₀ hm₀ using hex'
  let mm : (M →+* ℂ) → Multiset ℂ := fun σ => if σ = τ then m else if σ = τ' then m' else m₀ σ
  have e1 : mm τ = m := if_pos rfl
  have e2 : mm τ' = m' := by
    change (if τ' = τ then m else if τ' = τ' then m' else m₀ τ') = m'
    rw [if_neg hne.symm, if_pos rfl]
  have hmm : ∀ σ, π.HasInfChar σ (mm σ) := by
    intro σ
    by_cases a : σ = τ
    · rw [a, e1]; exact hm
    by_cases b : σ = τ'
    · rw [b, e2]; exact hm'
    · change π.HasInfChar σ (if σ = τ then m else if σ = τ' then m' else m₀ σ)
      rw [if_neg a, if_neg b]
      exact hm₀ σ
  let rs : (M →+* ℂ) → (K →+* ℂ) := fun σ => σ.comp (algebraMap K M)
  let A : (K →+* ℂ) → Multiset ℂ := fun φ => ∑ σ with rs σ = φ, mm σ
  have key : ∀ k : ℕ, ∑ φ, (mP φ).map (· + k * expo χ φ) = ∑ φ, (A φ).map (· + k * expo χ φ) := by
    intro k
    have h := hUnion K M h2 (P.twist (χ ^ k)) (π.twist (ξ ^ k)) (indSys_twist h2 hI χ ξ hξv k)
      (fun φ => (mP φ).map (· + expo (χ ^ k) φ)) (fun σ => (mm σ).map (· + expo (ξ ^ k) σ))
      (fun φ => (hmP φ).twist _) (fun σ => (hmm σ).twist _)
    simp only [GlobalTheory.BCT.TwistDisc.expo_pow, hξe] at h
    rw [h, ← Finset.sum_fiberwise Finset.univ rs]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [map_sum']
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [← (Finset.mem_filter.1 hσ).2]
  have hA := congrFun (hSep (K →+* ℂ) (expo χ) hχ mP A key) (τ.comp (algebraMap K M))
  have hf : (Finset.univ.filter fun σ => rs σ = τ.comp (algebraMap K M)) = {τ, τ'} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun h => over_two h2 hne hres.symm h, ?_⟩
    rintro (rfl | rfl)
    · rfl
    · exact hres.symm
  have hS : A (τ.comp (algebraMap K M)) = m + m' := by
    change ∑ σ with rs σ = τ.comp (algebraMap K M), mm σ = m + m'
    rw [hf, Finset.sum_pair hne, e1, e2]
  rw [← hS, ← hA]
  exact hmP _

end UpperTheory.V.Z.Inf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideOf
section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K]

private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem sum_shift {ι : Type} [Fintype ι] (m : ι → Multiset ℂ) (z : ℂ) :
    (∑ τ, (m τ).map (· + z)).map (· - z) = ∑ τ, m τ := by
  rw [← Multiset.mapAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Multiset.map_map, Function.comp_def]

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.sideOf :
    UpperTheory.V.Z.Inf.SideOf := by
  intro hO hC K _ _ _ n hn σ m hm
  let x : GlobalTheory.ResW.Letter K := ⟨n, σ⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))
  let χ : HChar K := Model.absC K z
  have hspec := (GlobalTheory.ResW.letter_centralExponent K x).1
  have htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change lie K n (oneL K n) (mulChi n χ ψ) = 0
    rw [lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  have hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z) := fun v => by
    refine ⟨fun y hy => Units.ext ?_, ?_⟩
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (unif v)))) = _
      have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
        ← Complex.natCast_log]
      congr 1; push_cast; ring
  obtain ⟨S₀, hS⟩ := hC K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) (fun τ => (m τ).map (· + z)) (fun τ => by
    have h := (hm τ).twist χ
    rwa [show expo χ τ = z from Model.expo_absC z τ] at h)
  refine ⟨S₀, fun S hS₀ B hB => ?_⟩
  have hP := hS S hS₀ (fun w => (B w).map (· * χ.val w)) fun w hw => by
    have h := (hB w hw).twist (hval w).1
    rwa [CG.twist_mk] at h
  have hP2 := hO.2 _ _ _ z hP
  rw [sum_shift] at hP2
  have e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w =
      (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := fun w => by
    simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]
  have e' : cx (fun w => (B w).map (· * χ.val w)) =
      fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := funext e
  rw [e'] at hP2
  simpa only [euler_shift, eulerd_shift] using hP2
end

