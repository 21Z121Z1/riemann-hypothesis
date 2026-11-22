import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import GroundTheory.AutomorphicForms.SmoothRep

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CharDom
section
noncomputable section

open ValuativeRel
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem indep {T : Type} [CommGroup T] (M : Submonoid T) (hM : ∀ t : T, ∃ s ∈ M, s * t ∈ M) (t₀ : T)
    (E E' : Multiset (T →* ℂˣ)) (c c' : ℂ) (hc : c ≠ 0)
    (h : ∀ t ∈ M, c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) :
    ∀ μ ∈ E, μ ∈ E' := by
  classical
  let ρ : (T →* ℂˣ) → (M →* ℂ) := fun μ => (Units.coeHom ℂ).comp (μ.comp M.subtype)
  have hρm : ∀ μ (m : M), ρ μ m = (μ m : ℂ) := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro μ ν hμν
    have hM' : ∀ m ∈ M, μ m = ν m := by
      intro m hm
      apply Units.ext
      have := DFunLike.congr_fun hμν ⟨m, hm⟩
      rw [hρm, hρm] at this
      exact this
    refine MonoidHom.ext fun t => ?_
    obtain ⟨s, hs, hst⟩ := hM t
    have e : t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
    rw [e, map_mul μ, map_mul ν, map_inv μ, map_inv ν, hM' s hs, hM' _ hst]
  have hli : LinearIndependent ℂ (fun μ : T →* ℂˣ => ((ρ μ : M →* ℂ) : M → ℂ)) :=
    (linearIndependent_monoidHom M ℂ).comp ρ hρinj
  intro μ hμ
  by_contra hμ'
  let S := (E + E').toFinset
  let g : (T →* ℂˣ) → ℂ := fun ν => (c * E.count ν - c' * E'.count ν) * (ν t₀ : ℂ)
  have conv : ∀ F : Multiset (T →* ℂˣ), F.toFinset ⊆ S → ∀ t : T,
      (F.map fun ν => (ν (t₀ * t) : ℂ)).sum = ∑ ν ∈ S, (F.count ν : ℂ) * ((ν t₀ : ℂ) * (ν t : ℂ)) := by
    intro F hF t
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hF]
    · apply Finset.sum_congr rfl
      intro ν _
      rw [nsmul_eq_mul, map_mul, Units.val_mul]
    · intro ν _ hν
      rw [Multiset.count_eq_zero.mpr (by simpa using hν)]
      simp
  have hsum : ∑ ν ∈ S, g ν • ((ρ ν : M →* ℂ) : M → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := h m m.2
    rw [conv E (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_toFinset.mp hx)))) m,
      conv E' (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_toFinset.mp hx)))) m,
      Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hρm]
    simp only [g]
    ring
  have h0 := linearIndependent_iff'.mp hli S g hsum μ
    (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl hμ)))
  simp only [g, Multiset.count_eq_zero.mpr hμ', Nat.cast_zero, mul_zero, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact (Multiset.count_pos.mpr hμ).ne' (by exact_mod_cast h3)
  · exact (μ t₀).ne_zero h2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def domM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Submonoid (Fin n → kˣ) where
  carrier := {t | Dom t}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)
  one_mem' := by
    intro i j _
    simp

private theorem dom_translate (t : Fin n → kˣ) : ∃ s ∈ domM k n, s * t ∈ domM k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, (domM k 0).one_mem, ?_⟩
    show Dom _
    intro i
    exact i.elim0
  · obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
      (fun p => valuation k ((t p.1 / t p.2 : kˣ) : k)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    have hx1 : 1 ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) := by
      have := hp (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simpa using this
    have hxt : ∀ i j, valuation k (t i : k) ≤
        valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k) := by
      intro i j
      have := hp (i, j) (Finset.mem_univ _)
      have e : (t i : k) = ((t i / t j : kˣ) : k) * (t j : k) := by simp
      rw [e, map_mul]
      gcongr
    refine ⟨fun i => (t p.1 / t p.2) ^ (i : ℕ), ?_, ?_⟩
    · show Dom _
      intro i j hij
      simp only [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_right₀ hx1 (le_of_lt hij)
    · show Dom _
      intro i j hij
      simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      have hij' : (i : ℕ) + 1 ≤ j := hij
      have hpw := pow_le_pow_right₀ hx1 hij'
      calc valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) * valuation k (t i : k)
          ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) *
            (valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k)) := by
            gcongr
            exact hxt i j
        _ = valuation k ((t p.1 / t p.2 : kˣ) : k) ^ ((i : ℕ) + 1) * valuation k (t j : k) := by
            rw [pow_succ, mul_assoc]
        _ ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (j : ℕ) * valuation k (t j : k) := by
            gcongr

theorem charDom : CharDom := by
  intro k _ _ _ _ n t₀ E E' c c' hc h
  have hind := indep (domM k n) (fun t => dom_translate t) t₀ E E' c c' hc h
  refine ⟨hind, fun hE => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hE
  have := indep (domM k n) (fun t => dom_translate t) t₀ E 0 1 0 one_ne_zero
    (fun t ht => by rw [one_mul, hne t ht]; simp) μ hμ
  simp at this

end UpperTheory.Gal.Join
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosOp
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem mem_dcos_iff {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t)
    (g : GL (Fin n) k) :
    g ∈ dcos K t ↔ ∃ u ∈ unipB k (Fin n), u ∈ K ∧ ∃ i ∈ K, g = u * diagT k (Fin n) t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact a ha
  refine ⟨u, hu.2, hu.1, _, mul_mem (mul_mem hd (hK.low t ht c hc)) hb, ?_⟩
  have e : diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t := by
    rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k (Fin n) d * c * diagT k (Fin n) t * b
      = u * (diagT k (Fin n) d * diagT k (Fin n) t) * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) * b := by
        group
    _ = _ := by rw [← e]; group

private theorem dcos_eq_image (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) :
    dcos K t = (fun x : GL (Fin n) k × GL (Fin n) k => x.1 * diagT k (Fin n) t * x.2) ''
      ((K : Set (GL (Fin n) k)) ×ˢ (K : Set (GL (Fin n) k))) := by
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

private theorem isCompact_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsCompact (dcos K t) := by
  rw [dcos_eq_image]
  exact (hK.1.prod hK.1).image (by fun_prop)

private theorem isOpen_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsOpen (dcos K t) := by
  have e : dcos K t = ⋃ a ∈ (K : Set (GL (Fin n) k)),
      (fun g => (a * diagT k (Fin n) t) * g) '' (K : Set (GL (Fin n) k)) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
  rw [e]
  exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * diagT k (Fin n) t)).isOpenMap _ hK.2

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem isClosed_unipB : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  have e : (unipB k (Fin n) : Set (GL (Fin n) k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) k | g.val i j = 0}) ∩
      ⋂ i, {g : GL (Fin n) k | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact mem_unipB k
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in

private theorem measure_dcos [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t) :
    μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹ := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  letI : MeasurableSpace (unipRad k (points (Fin n))) := _root_.borel _
  haveI : BorelSpace (unipRad k (points (Fin n))) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).secondCountableTopology
  let ν : Measure (unipRad k (points (Fin n))) := Measure.haar
  have ho : IsOpen {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hK.co.2.preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points (Fin n)) : Set (GL (Fin n) k)) := isClosed_unipB
  have hc : IsCompact {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK.co.1
  have h1 := measure_mul_eq μ ν hK.co.2 (t := diagT k (Fin n) t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => hK.up t ht u ⟨hI, hu⟩)
    (isCompact_dcos hK.co t).measurableSet (mem_dcos_iff hK ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) ν
    (leviTorus k (Fin n) t) _ ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (dcos K t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem K⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

end

end UpperTheory.Gal.Join

theorem UpperTheory.Gal.Join.dcosVol :
    UpperTheory.Gal.Join.DcosVol := by
  intro k _ _ _ _ n _ _ μ _ K hK t ht
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc := isCompact_dcos hK.co t
  refine ⟨⟨(LocallyConstant.indicator (1 : LocallyConstant (GL (Fin n) k) ℂ) ⟨hc.isClosed, isOpen_dcos hK.co t⟩).2,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, measure_dcos μ hK ht⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section Mean

open GroundTheory.Automorphic (stabilizerOf mem_stabilizerOf)

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private noncomputable def mean (T : Subgroup H) [T.FiniteIndex] (v : V) : V :=
  (Nat.card (H ⧸ T) : ℂ)⁻¹ • ∑ q : H ⧸ T, ρ q.out v

private theorem card_ne (T : Subgroup H) [T.FiniteIndex] : (Nat.card (H ⧸ T) : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Subgroup.FiniteIndex.index_ne_zero

private theorem out_apply {T : Subgroup H} {v : V} (hv : ∀ t ∈ T, ρ t v = v) (x : H) :
    ρ (x : H ⧸ T).out v = ρ x v := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T x
  rw [ht, map_mul, Module.End.mul_apply, hv t t.2]

private theorem mean_eq {T' T : Subgroup H} [T'.FiniteIndex] [T.FiniteIndex] (hle : T' ≤ T) {v : V}
    (hv : ∀ t ∈ T, ρ t v = v) : mean ρ T' v = mean ρ T v := by
  unfold mean
  have hcard : Nat.card (H ⧸ T') = Nat.card (H ⧸ T) * Nat.card (T ⧸ T'.subgroupOf T) := by
    rw [Nat.card_congr (Subgroup.quotientEquivProdOfLE hle), Nat.card_prod]
  have hsum : ∑ q : H ⧸ T', ρ q.out v =
      ∑ x : (H ⧸ T) × (T ⧸ T'.subgroupOf T), ρ x.1.out v := by
    refine Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ _ ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.quotientEquivProdOfLE_apply]
    show ρ (x : H ⧸ T').out v = ρ (x : H ⧸ T).out v
    rw [out_apply ρ (fun t ht => hv t (hle ht)), out_apply ρ hv]
  have hm : (Nat.card (T ⧸ T'.subgroupOf T) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [hsum, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]

private theorem mean_mem {T : Subgroup H} [T.FiniteIndex] {v : V} (hv : ∀ t ∈ T, ρ t v = v) (h : H) :
    ρ h (mean ρ T v) = mean ρ T v := by
  unfold mean
  rw [map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((h * q.out : H) : H ⧸ T) = h • q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (h * q.out), hq]
  rfl

private theorem mean_lin {W : Type} [AddCommGroup W] [Module ℂ W] (T : Subgroup H) [T.FiniteIndex]
    (p : V →ₗ[ℂ] W) {v : V} (hp : ∀ h, p (ρ h v) = p v) : p (mean ρ T v) = p v := by
  simp only [mean, map_smul, map_sum, hp, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne T), one_smul]

private theorem mean_add (T : Subgroup H) [T.FiniteIndex] (x y : V) :
    mean ρ T (x + y) = mean ρ T x + mean ρ T y := by
  simp only [mean, map_add, Finset.sum_add_distrib, smul_add]

private theorem mean_smul (T : Subgroup H) [T.FiniteIndex] (c : ℂ) (x : V) :
    mean ρ T (c • x) = c • mean ρ T x := by
  simp only [mean, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem mean_act {T : Subgroup H} [T.FiniteIndex] [T.Normal] {v : V} (hv : ∀ t ∈ T, ρ t v = v)
    (h : H) : mean ρ T (ρ h v) = mean ρ T v := by
  unfold mean
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight (h : H ⧸ T)) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((q.out * h : H) : H ⧸ T) = q * (h : H ⧸ T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (q.out * h), hq]
  rfl

private theorem exists_avg (hfin : ∀ v, (stabilizerOf ρ v).FiniteIndex) : ∃ e : V →ₗ[ℂ] V,
    (∀ h v, ρ h (e v) = e v) ∧ (∀ h v, e (ρ h v) = e v) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V),
        (∀ h, p (ρ h v) = p v) → p (e v) = p v := by
  let E : V → V := fun v => @mean H V _ _ _ ρ (stabilizerOf ρ v) (hfin v) v
  have hE : ∀ (v : V) (T : Subgroup H) [T.FiniteIndex], T ≤ stabilizerOf ρ v → E v = mean ρ T v := by
    intro v T _ hle
    haveI := hfin v
    exact (mean_eq ρ hle (fun t ht => mem_stabilizerOf.1 ht)).symm
  have hfx : ∀ v, ∀ t ∈ stabilizerOf ρ v, ρ t v = v := fun v t ht => mem_stabilizerOf.1 ht
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    haveI := hfin x
    haveI := hfin y
    haveI := hfin (x + y)
    show E (x + y) = E x + E y
    rw [hE (x + y) (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_left),
      hE y (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_right),
      mean_add]
  · intro c x
    haveI := hfin x
    haveI := hfin (c • x)
    show E (c • x) = c • E x
    rw [hE (c • x) (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_left, mean_smul]
  · intro h v
    haveI := hfin v
    exact mean_mem ρ (hfx v) h
  · intro h v
    haveI := hfin v
    haveI := hfin (ρ h v)
    have hle : (stabilizerOf ρ v).normalCore ≤ stabilizerOf ρ (ρ h v) := by
      intro t ht
      rw [mem_stabilizerOf]
      have h1 : h⁻¹ * t * h ∈ (stabilizerOf ρ v).normalCore := by
        have := (Subgroup.normalCore_normal (stabilizerOf ρ v)).conj_mem t ht h⁻¹
        simpa using this
      have h2 := hfx v _ (Subgroup.normalCore_le _ h1)
      calc ρ t (ρ h v) = ρ (t * h) v := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (h * (h⁻¹ * t * h)) v := by rw [show h * (h⁻¹ * t * h) = t * h by group]
        _ = ρ h (ρ (h⁻¹ * t * h) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ h v := by rw [h2]
    show E (ρ h v) = E v
    rw [hE (ρ h v) _ hle, hE v _ (Subgroup.normalCore_le _),
      mean_act ρ (fun t ht => hfx v t (Subgroup.normalCore_le _ ht)) h]
  · intro W _ _ p v hp
    haveI := hfin v
    exact mean_lin ρ _ p hp

end Mean

theorem UpperTheory.Gal.Join.avgEx :
    UpperTheory.Gal.Join.AvgEx := by
  intro G V _ _ _ _ _ π hsm K hK
  unfold IsSmooth at hsm
  unfold CO at hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  let ρ : Representation ℂ K V := π.comp K.subtype
  have hfin : ∀ v, (GroundTheory.Automorphic.stabilizerOf ρ v).FiniteIndex := by
    intro v
    haveI := Subgroup.quotient_finite_of_isOpen (GroundTheory.Automorphic.stabilizerOf ρ v) ((hsm v).preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨e, he1, he2, he3⟩ := exists_avg ρ hfin
  have hfix : ∀ w, (∀ g ∈ K, π g w = w) → e w = w := by
    intro w hw
    have := he3 V LinearMap.id w (fun h => hw h h.2)
    simpa using this
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro g hg
    exact he1 ⟨g, hg⟩ v
  · intro v hv
    rw [GlobalTheory.Parabolic.mem_fixed] at hv
    exact hfix v hv
  · intro g hg v
    exact he2 ⟨g, hg⟩ v
  · intro W _ _ p v hp
    exact he3 W p v (fun h => hp h h.2)
  · intro s A hA hs hsurj v
    have h1 : e (A (e v)) = A (e v) := by
      apply hfix
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hsurj g hg
      rw [← hA]
      congr 1
      exact he1 ⟨h, hh⟩ v
    have h2 : e (A (e v)) = e (A v) := by
      refine he3 V (e ∘ₗ A) v (fun h => ?_)
      show e (A (π h v)) = e (A v)
      rw [hA]
      exact he2 ⟨s h, hs h h.2⟩ (A v)
    rw [← h1, h2]
end

