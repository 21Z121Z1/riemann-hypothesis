import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacy
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppCent

theorem comm_of_conj {G : Type} [Group G] (γ p₀ q : G)
    (h : q⁻¹ * (p₀⁻¹ * γ * p₀) * q = p₀⁻¹ * γ * p₀) :
    (p₀ * q * p₀⁻¹) * γ = γ * (p₀ * q * p₀⁻¹) := by
  calc (p₀ * q * p₀⁻¹) * γ = p₀ * q * (p₀⁻¹ * γ * p₀) * p₀⁻¹ := by group
    _ = p₀ * q * (q⁻¹ * (p₀⁻¹ * γ * p₀) * q) * p₀⁻¹ := by rw [h]
    _ = γ * (p₀ * q * p₀⁻¹) := by group

theorem conj_comm {G : Type} [Group G] (γ p₀ t : G) (h : t * γ = γ * t) :
    (p₀⁻¹ * t * p₀)⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * t * p₀) = p₀⁻¹ * γ * p₀ := by
  calc _ = p₀⁻¹ * t⁻¹ * (γ * t) * p₀ := by group
    _ = p₀⁻¹ * t⁻¹ * (t * γ) * p₀ := by rw [h]
    _ = _ := by group

theorem isCompact_closure_zpowers_conj {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (c t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (c⁻¹ * t * c) : Set G)) := by
  have hφ : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hK := h.image hφ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), ?_⟩
  have e : c⁻¹ * t * c = MulAut.conj c⁻¹ t := by simp [MulAut.conj_apply]
  have e' : ∀ x : G, c⁻¹ * x * c = MulAut.conj c⁻¹ x := fun x => by simp [MulAut.conj_apply]
  simp only [e', map_zpow]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ ⟨p1, hp1⟩
  obtain ⟨hW1, hW2, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hinj : Function.Injective (wexp n l) :=
    (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1.injective
  have huc := GlobalTheory.CompanionTheory.UnitaryContraction.main E hU w hw n b hb ϖ hϖ l hl hyp
  obtain ⟨m, hm, u, hu, hmu⟩ := huc _ hp1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UL n w, p₀ = p1 * m := ⟨_, rfl⟩
  have hγ0 : (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
    rw [← hmu]
    congr 1
    rw [hp₀]
    group

  have key : ∀ (q : UL n w) (u' : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u' i : w.adicCompletion E) = wexp n l i) →
      (q⁻¹ * (p₀⁻¹ * γ * p₀) * q).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ →
      u = u' ∧ ∃ s : Fin n → (w.adicCompletion E)ˣ,
        q.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * b⁻¹ := by
    intro q u' hu' e
    have e' : q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1 =
        b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ := by
      rw [← hγ0, ← e]
      rfl
    have hh : (b⁻¹ * q.1 * b)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (b⁻¹ * q.1 * b) =
        GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' := by
      calc _ = b⁻¹ * (q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1) * b := by
            group
        _ = _ := by rw [e']; group
    obtain ⟨h1, s, hs⟩ := GlobalTheory.CompanionTheory.DiagRigid.diag_rigid (w.adicCompletion E) n (wexp n l) hinj u u'
      hu hu' _ hh
    refine ⟨h1, s, ?_⟩
    rw [← hs]
    group
  refine ⟨p₀, u, hu, hγ0, fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨m', hm', u', hu', e⟩ := huc _ hp
    have e2 : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = m'⁻¹ * (p⁻¹ * γ * p) * m' := by
      group
    obtain ⟨rfl, -⟩ := key (p₀⁻¹ * p * m') u' hu' (by rw [e2]; exact e)
    have hq : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = p₀⁻¹ * γ * p₀ := by
      apply Subtype.ext
      rw [e2, e, hγ0]
    refine ⟨p₀ * (p₀⁻¹ * p * m') * p₀⁻¹, comm_of_conj γ p₀ _ hq, m'⁻¹, inv_mem hm', ?_⟩
    group
  ·
    rintro ⟨z, hz, i, hi, rfl⟩
    have hz' : z * γ = γ * z := hz
    have e : (z * p₀ * i)⁻¹ * γ * (z * p₀ * i) = i⁻¹ * (p₀⁻¹ * γ * p₀) * i := by
      calc _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (γ * z) * p₀ * i := by group
        _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (z * γ) * p₀ * i := by rw [hz']
        _ = _ := by group
    rw [e, GlobalTheory.CompanionTheory.DiagCoset.fU_diag E hU w hw n b hb ϖ hϖ l hl _ u hu hγ0 _ (inv_mem hi) _ hi]
    exact one_ne_zero
  ·
    refine GlobalTheory.CompanionTheory.CptGen.cptPart_eq_inf (UL n w) _ _ ?_ ?_
    · rw [Subgroup.coe_map]
      refine hWc.image ?_
      change Continuous fun x : UL n w => p₀ * x * p₀⁻¹
      fun_prop
    · intro t ht hc
      have ht' : t * γ = γ * t := ht
      obtain ⟨-, s, hs⟩ := key (p₀⁻¹ * t * p₀) u hu (by rw [conj_comm γ p₀ t ht']; exact hγ0)
      have hv := GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers E w n (UL n w)
        (p₀⁻¹ * t * p₀) b s hs (isCompact_closure_zpowers_conj p₀ t hc)
      have hmem : p₀⁻¹ * t * p₀ ∈ iwU n w b := by
        rw [hW2]
        have : b⁻¹ * (p₀⁻¹ * t * p₀).1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by
          rw [hs]
          group
        rw [this]
        exact GlobalTheory.CompanionTheory.DiagCoset.diagT_mem_iwGL w n s hv
      refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.CompanionTheory.SuppCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecond
section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar partialLFunction)

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinEuler

open Classical in

def partialTerm (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) : Ideal (𝓞 ℚ) →* ℂ where
  toFun I := if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0
  map_one' := by
    have h : ∀ v ∈ S, ¬ v.asIdeal ∣ (1 : Ideal (𝓞 ℚ)) := fun v _ hv =>
      v.isPrime.ne_top (Ideal.isUnit_iff.1 (isUnit_of_dvd_one hv))
    rw [if_pos h, map_one]
  map_mul' I J := by
    have hp : ∀ v : Pl, v.asIdeal ∣ I * J ↔ v.asIdeal ∣ I ∨ v.asIdeal ∣ J := fun v =>
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).dvd_mul
    by_cases hI : ∀ v ∈ S, ¬ v.asIdeal ∣ I
    · by_cases hJ : ∀ v ∈ S, ¬ v.asIdeal ∣ J
      · have hIJ : ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun v hv h =>
          ((hp v).1 h).elim (hI v hv) (hJ v hv)
        rw [if_pos hIJ, if_pos hI, if_pos hJ, map_mul]
      · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
          hJ fun v hv hd => h v hv ((hp v).2 (Or.inr hd))
        rw [if_neg hIJ, if_neg hJ, mul_zero]
    · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
        hI fun v hv hd => h v hv ((hp v).2 (Or.inl hd))
      rw [if_neg hIJ, if_neg hI, zero_mul]

open Classical in
theorem partialTerm_apply (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) (I : Ideal (𝓞 ℚ)) :
    partialTerm c S s I = if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0 :=
  rfl

theorem norm_partialTerm_le (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) (I : Ideal (𝓞 ℚ)) :
    ‖partialTerm c S s I‖ ≤ ‖c.coeffTerm s I‖ := by
  rw [partialTerm_apply]
  split_ifs
  · exact le_rfl
  · simp

theorem partialTerm_bot (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) :
    partialTerm c S s ⊥ = 0 := by
  have h := norm_partialTerm_le c S s ⊥
  rw [c.coeffTerm_bot, norm_zero] at h
  exact norm_le_zero_iff.1 h

theorem tsum_partialTerm (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) :
    ∑' I, partialTerm c S s I = partialLFunction c S s := by
  rw [partialLFunction]
  refine tsum_congr fun I => ?_
  rw [partialTerm_apply, HeckeCharacter.coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]
  split_ifs
  · rfl
  · simp

theorem valued_unifUnit (v : Pl) :
    Valued.v ((unifUnit (Qv v) : (Qv v)ˣ) : Qv v) = WithZero.exp (-1 : ℤ) := by
  rw [valued_eq_exp_neg_ord (unifUnit (Qv v)).ne_zero, ord_unifUnit]

theorem localLFactor_eq (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) {v : Pl} (hv : v ∉ S)
    (hu : IsUnramifiedChar (localChar c v)) :
    localLFactor (localChar c v) s = (1 - partialTerm c S s v.asIdeal)⁻¹ := by
  have hnd : ¬ v.asIdeal ∣ c.conductor := (c.isUnramifiedChar_localChar_iff v).1 hu
  have hS : ∀ w ∈ S, ¬ w.asIdeal ∣ v.asIdeal := fun w hw h =>
    hv (heightOneSpectrum_eq_of_dvd h ▸ hw)
  rw [localLFactor_of_isUnramified hu, partialTerm_apply, if_pos hS,
    HeckeCharacter.coeffTerm_apply, c.coeff_asIdeal_eq_toIdele hnd (valued_unifUnit v),
    residueCard_adicCompletion, Complex.cpow_neg, div_eq_mul_inv]
  rfl

theorem hasProd_partial (c : HeckeCharacter ℚ) (S : Finset Pl) {s : ℂ} (hs : 1 < s.re)
    (hun : ∀ v ∉ S, IsUnramifiedChar (localChar c v)) :
    HasProd (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s)
      (partialLFunction c S s) := by
  have hsum : Summable fun I => ‖partialTerm c S s I‖ :=
    (c.summable_norm_coeffTerm hs).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_partialTerm_le c S s)
  have h := hasProd_euler (partialTerm c S s) hsum (partialTerm_bot c S s)
  rw [tsum_partialTerm] at h
  rw [← hasProd_subtype_iff_of_mulSupport_subset (s := {v : Pl | v ∉ S})] at h
  · have hfun : (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s) =
        fun v : {v : Pl // v ∉ S} => (1 - partialTerm c S s v.1.asIdeal)⁻¹ :=
      funext fun v => localLFactor_eq c S s v.2 (hun v.1 v.2)
    rw [hfun]
    exact h
  · intro v hv
    by_contra hvS
    have hvS' : v ∈ S := by simpa using hvS
    apply hv
    have h0 : partialTerm c S s v.asIdeal = 0 := by
      rw [partialTerm_apply, if_neg fun h => h v hvS' dvd_rfl]
    simp [h0]

theorem norm_localLFactor_sub_one_le {s : ℂ} (hs : 1 < s.re) {v : Pl} {ν : (Qv v)ˣ →* ℂˣ}
    (hν : IsUnit1 ν) :
    ‖localLFactor ν s - 1‖ ≤ 2 * ((Ideal.absNorm v.asIdeal : ℝ) ^ s.re)⁻¹ := by
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← residueCard_adicCompletion]
    exact_mod_cast one_lt_residueCard (K := Qv v)
  have hqpos : 0 < Ideal.absNorm v.asIdeal := by
    have : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
    exact_mod_cast this
  set t : ℝ := ((Ideal.absNorm v.asIdeal : ℝ) ^ s.re)⁻¹ with ht
  have htpos : 0 < t := inv_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
  by_cases hu : IsUnramifiedChar ν
  · rw [localLFactor_of_isUnramified hu, residueCard_adicCompletion]
    set x : ℂ := ((ν (unifUnit (Qv v)) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hx
    have hxn : ‖x‖ = t := by
      rw [hx, norm_mul, hν.2, one_mul, Complex.norm_natCast_cpow_of_pos hqpos, Complex.neg_re,
        Real.rpow_neg (by linarith)]
    have hthalf : t ≤ 1 / 2 := by
      rw [ht, one_div]
      refine inv_anti₀ (by norm_num) ?_
      calc (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := hq2
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    have h1 : (1 : ℝ) / 2 ≤ ‖1 - x‖ := by
      have := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one, hxn] at this
      linarith
    have hne : 1 - x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      norm_num at h1
    have he : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
      field_simp
      ring
    rw [he, norm_mul, norm_inv, hxn, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ htpos.le
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  · rw [localLFactor_of_not_isUnramified hu, sub_self, norm_zero]
    positivity

theorem multipliable_local (S : Finset Pl) {s : ℂ} (hs : 1 < s.re) (ν : ∀ v : Pl, (Qv v)ˣ →* ℂˣ)
    (hν : ∀ v, IsUnit1 (ν v)) :
    Multipliable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s := by
  have hinj : Function.Injective fun v : {v : Pl // v ∉ S} => v.1.asIdeal :=
    fun v w h => Subtype.ext (HeightOneSpectrum.ext h)
  have hb : Summable fun v : {v : Pl // v ∉ S} =>
      2 * ((Ideal.absNorm v.1.asIdeal : ℝ) ^ s.re)⁻¹ :=
    ((summable_absNorm_rpow_inv (K := ℚ) hs).comp_injective hinj).mul_left 2
  have hf : Summable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s - 1 :=
    Summable.of_norm_bounded hb fun v => norm_localLFactor_sub_one_le hs (hν v.1)
  simpa using Complex.multipliable_one_add_of_summable hf

theorem e2 (_ : Ad3.R.B0) : Ad3.R.E2 := by
  intro S s hs
  refine ⟨fun c hc => ⟨fun v hv => ?_, hasProd_partial c S hs hc⟩,
    fun ν hν => multipliable_local S hs ν hν⟩
  by_contra hvS
  exact (c.isUnramifiedChar_localChar_iff v).1 (hc v hvS) hv

end GlobalTheory.CompanionTheory.RankinEuler

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3 Ad3.R
open scoped Classical

namespace GlobalTheory.CompanionTheory.RankinWhittaker

theorem prodEquiv_realEmb (x : GL (Fin 2) ℝ) :
    AdelicGLn.prodEquiv ℚ 2 (realEmb x) = (GL2Classical.realInf x, 1) :=
  (AdelicGLn.prodEquiv ℚ 2).apply_symm_apply _

theorem realPart_congr {g g' : G2} (h : ∀ w, infAt w g = infAt w g') : realPart g = realPart g' := by
  have e : (AdelicGLn.prodEquiv ℚ 2 g).1 = (AdelicGLn.prodEquiv ℚ 2 g').1 := by
    ext a b
    change (g a b).1 = (g' a b).1
    funext w
    have := congrArg (fun x : GL (Fin 2) w.Completion => x a b) (h w)
    simpa using this
  simp only [GL2Classical.realPart, e]

theorem infAt_realEmb_realPart (g : G2) (w : InfinitePlace ℚ) : infAt w (realEmb (realPart g)) = infAt w g := by
  have e : (AdelicGLn.prodEquiv ℚ 2 (realEmb (realPart g))).1 = (AdelicGLn.prodEquiv ℚ 2 g).1 := by
    rw [prodEquiv_realEmb]
    ext a b
    simp [GL2Classical.realPart, GL2Classical.realInf]
  change (AdelicGLn.infiniteEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (realEmb (realPart g))).1) w =
    (AdelicGLn.infiniteEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 g).1) w
  rw [e]

theorem finAt_realEmb (x : GL (Fin 2) ℝ) (v : Pl) : finAt v (realEmb x) = 1 := by
  have e : (AdelicGLn.prodEquiv ℚ 2 (realEmb x)).2 = 1 := by
    rw [prodEquiv_realEmb]
  change (AdelicGLn.finiteRestrictedEquiv ℚ 2 (AdelicGLn.prodEquiv ℚ 2 (realEmb x)).2) v = 1
  rw [e, map_one]
  rfl

theorem Wh_mul_right {φ : G2 → ℂ} {κ : G2} (h : ∀ g, φ (g * κ) = φ g) (g : G2) : Wh φ (g * κ) = Wh φ g := by
  unfold Wh
  simp only [← mul_assoc, h]

theorem Wh_eq_prod {N : ℕ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    {μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ} {φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ}
    (hglob : ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g)
    (hmod : Mod N ω (Wh φ) μ₁ μ₂ φ₀) (hloc : ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h, IsLoc2 v x h)
    (T : Finset Pl) : ∀ g : G2, (∀ v ∉ T, finAt v g ∈ integralGL (Qv v) 2 ∧ (pOf v ∣ N → finAt v g = 1)) →
      Wh φ g = Wh φ (realEmb (realPart g)) *
        ∏ v ∈ T, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g) := by
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hinf : ∀ w, infAt w ((realEmb (realPart g))⁻¹ * g) = 1 := fun w => by
      rw [Reduction.infAt_mul, Reduction.infAt_inv, infAt_realEmb_realPart, inv_mul_cancel]
    have hfin : ∀ v, finAt v ((realEmb (realPart g))⁻¹ * g) = finAt v g := fun v => by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, finAt_realEmb, inv_one, one_mul]
    have hκ : (realEmb (realPart g))⁻¹ * g ∈ (maxCompact : Subgroup G2) :=
      ⟨fun w => by rw [hinf w]; exact one_mem _, fun v => by
        rw [hfin v]; exact (hg v (by simp)).1⟩
    have h := Wh_mul_right (hglob ⟨_, hκ⟩ hinf (fun v hv => by
      change finAt v ((realEmb (realPart g))⁻¹ * g) = 1
      rw [hfin v]; exact (hg v (by simp)).2 hv)) (realEmb (realPart g))
    simp only [mul_inv_cancel_left] at h
    simpa using h
  | insert v T hv ih =>
    intro g hg
    obtain ⟨h, hh⟩ := hloc v (finAt v g)
    have hv1 : finAt v (g * h⁻¹) = 1 := by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, hh.1, mul_inv_cancel]
    have hoth : ∀ v', v' ≠ v → finAt v' (g * h⁻¹) = finAt v' g := fun v' hne => by
      rw [Reduction.finAt_mul, Reduction.finAt_inv, hh.2.1 v' hne, inv_one, mul_one]
    have hinf : ∀ w, infAt w (g * h⁻¹) = infAt w g := fun w => by
      rw [Reduction.infAt_mul, Reduction.infAt_inv, hh.2.2 w, inv_one, mul_one]
    have hfac := hmod.fac v (g * h⁻¹) hv1 (finAt v g) h hh
    rw [inv_mul_cancel_right] at hfac
    have hoff : ∀ v' ∉ T, finAt v' (g * h⁻¹) ∈ integralGL (Qv v') 2 ∧ (pOf v' ∣ N → finAt v' (g * h⁻¹) = 1) := by
      intro v' hv'
      by_cases e : v' = v
      · subst e
        exact ⟨by rw [hv1]; exact one_mem _, fun _ => hv1⟩
      · rw [hoth v' e]
        exact hg v' (by simp [e, hv'])
    rw [hfac, ih _ hoff, realPart_congr hinf, Finset.prod_insert hv,
      Finset.prod_congr rfl (fun v' hv' => by
        rw [hoth v' (fun e => hv (e ▸ hv'))])]
    ring

theorem whittaker_factorisation : B0 → M0 → F3 → E0 := by
  intro hB hM hF k N _ h3 χ hχ f a hform heig ω φ hom hlift μ₁ μ₂ φ₀ hmod g
  obtain ⟨h1, hinj, -, -, -, -, hfin, -⟩ := hB
  have hH : Hk k N a ω φ := hF k N h3 χ hχ f a hform heig ω φ hom hlift
  have hbad : {v : Pl | pOf v ∣ N}.Finite :=
    ((Finset.finite_toSet (Nat.divisors N)).preimage hinj.injOn).subset fun v hv => by
      simpa [Nat.mem_divisors, NeZero.ne N] using hv
  have hT : ∀ v, v ∉ (hfin g).toFinset ∪ hbad.toFinset → finAt v g ∈ integralGL (Qv v) 2 ∧ ¬ pOf v ∣ N := by
    intro v hv
    simpa using hv
  rw [Wh_eq_prod hH.glob hmod (fun v => (h1 v).2.2.2.2.2.1) ((hfin g).toFinset ∪ hbad.toFinset) g
    (fun v hv => ⟨(hT v hv).1, fun hd => absurd hd (hT v hv).2⟩)]
  congr 1
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hvT
  apply hv
  obtain ⟨hint, hnb⟩ := hT v hvT
  obtain ⟨hu1, hu2, hφ⟩ := hmod.good v hnb
  beta_reduce
  rw [hφ]
  obtain ⟨-, hone, htype⟩ := hM (Qv v) (localAdelicChar ℚ v) (h1 v).1 (μ₁ v) (μ₂ v) (hmod.u₁ v) (hmod.u₂ v) hu1 hu2
  have h := htype.1 (finAt v g) hint 1
  rw [one_mul] at h
  rw [h, hone]

end GlobalTheory.CompanionTheory.RankinWhittaker

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingOfExponent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.GlFrob

set_option maxHeartbeats 1000000 in

theorem embedding_of_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hd1 : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible → ∀ (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n), (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), v ≠ 0 ∧ ∀ t : Levi k (fun _ : Fin n => Fin 1), v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd1) π t) (PositivityTheory.Lbc.torusChar ξ t)) → ∃ f : π.IntertwiningMap (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd), Function.Injective f := by
  intro k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv
  obtain ⟨v, hv0, hv⟩ := hv
  have h0 := GlobalTheory.CompanionTheory.KmIwahori.c0 k
  have h3 := GlobalTheory.CompanionTheory.Lbc.c3 k
  have hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1),
      jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' =
        jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * jac (stdBlocks (fun _ : Fin n => 1) hd1) π l := by
    intro l l'
    rw [← map_mul, ← map_mul]
    congr 1
    funext a
    exact GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _
  obtain ⟨hanti, hpow⟩ := GlobalTheory.T.deep_level_subgroups_filtration (k := k) n hd1
  have hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m,
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
        jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w := by
    intro w
    obtain ⟨m, hm, h⟩ := GlobalTheory.T.jacquet_vector_fixed_deep_level (k := k) n hd1 π hs w
    refine ⟨m - 1, ?_⟩
    rw [Nat.sub_add_cancel hm]
    exact h
  have hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
      LinearMap.ker (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1)) := by
    intro m
    haveI := GlobalTheory.T.jacquet_module_admissible_fixed (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)
    refine Submodule.finiteDimensional_of_le (S₂ := fixed (jac (stdBlocks (fun _ : Fin n => 1) hd1) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_
    intro w hw u
    have h1 := (Submodule.mem_iInf _).1 hw u
    have h2 : (jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0 := h1
    have h3' : jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w := by
      simpa [sub_eq_zero] using h2
    simpa using h3'
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.T.generalized_eigenvector_exists (Levi k (fun _ : Fin n => Fin 1))
    (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)))
    (jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm
    (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) hanti hpow hsm hfd
    (GlobalTheory.CompanionTheory.PinLift.torusCharHom ξ) v hv0 hv
  obtain ⟨g, w, hg⟩ := GlobalTheory.T.jacquet_cuspidal_support_of_functional n π ξ hξ hd f hf0 hf
  obtain ⟨G, x, hx⟩ := GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩
  refine ⟨G, ?_⟩
  have hso : IsSimpleOrder (Subrepresentation π) := hirr
  have hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0 := fun y => Iff.rfl
  rcases eq_bot_or_eq_top G.ker with h0' | h0'
  · refine (injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_
    have hy' : y ∈ G.ker.toSubmodule := (hk y).2 hy
    rw [h0'] at hy'
    exact (Submodule.mem_bot ℂ).1 hy'
  · refine absurd ((hk x).1 ?_) hx
    rw [h0']
    trivial

end GlobalTheory.CompanionTheory.GlFrob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_lintegral_limit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorizable_schwartz_orbital_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat <;> assumption)
end

