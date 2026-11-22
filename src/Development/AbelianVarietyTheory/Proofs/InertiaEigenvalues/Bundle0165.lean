import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaar
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_smul_vec [hU : Unram F E] {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]

def trForm [Unram F E] (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp only [star_add, add_dotProduct, map_add])
    (fun a c b => by simp only [star_smul_vec, smul_dotProduct, map_smul])
    (fun c b b' => by simp only [dotProduct_add, map_add])
    (fun a c b => by simp only [dotProduct_smul, map_smul])

theorem trForm_apply [Unram F E] {r : ℕ} (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trace_star [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z

theorem trForm_symm [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]

theorem trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1

theorem trForm_nondeg [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by
  refine ⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩
  rw [(trForm_symm r).eq]; exact h c

theorem kerL_eq [hU : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)}
    (hx : A.IsIsom x j) (y' y : A.L) :
    A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  obtain ⟨b⟩ := (GlobalTheory.JR.Et.quadratic_structure F E A).1
  haveI : Module.Free A.K A.L := Module.Free.of_basis b
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L
  unfold Et.kerL Et.psiK
  rw [hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]
  congr 2
  rw [show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul,
    smul_eq_mul]

end GlobalTheory.JR.MeasTransport

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem addChar_sum (ψ : AddChar F ℂ) {ι : Type} (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem pi_selfDual [hU : Unram F E] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) (M : Meas r F E) :
    letI := M.mE
    SelfDual (Measure.pi fun _ : Fin r => M.μE) (fun a b => ψ (trForm (F := F) r a b)) := by
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  let O : AddSubgroup (Fin r → E) :=
    { carrier := {v | ∀ i, ‖v i‖ ≤ 1}
      zero_mem' := by intro i; simp
      add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1 := fun v => Iff.rfl
  have hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1 := by
    ext v; simp [O, Set.mem_pi]
  have hOo : IsOpen (O : Set (Fin r → E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hOk : IsCompact (O : Set (Fin r → E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hdual : {y | ∀ x ∈ O, ψ (trForm (F := F) r x y) = 1} = (O : Set (Fin r → E)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]
    constructor
    · intro h i
      refine (hc (y i)).1 fun e he => ?_
      have h1 := h (Pi.single i (star e)) (by
        intro k
        by_cases hk : k = i
        · subst hk; simp [hU.norm_star, he]
        · simp [hk])
      rw [trForm_apply] at h1
      simpa [dotProduct, Pi.single_apply, apply_ite star] using h1
    · intro h x hx
      rw [trForm_apply, dotProduct, map_sum, addChar_sum]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [Pi.star_apply]
      exact (hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)
  have hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1 := by
    rw [hOset, Measure.pi_pi]; simp [M.volE]
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O
    hOo hOk |>.1
  rw [key, hdual, hvol, one_mul]

theorem map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]

theorem map_isIsom_eq_pi : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm

end GlobalTheory.JR.MeasTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModUniformiserCocyclesFiniteClassesLocal
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem modpi_cocycles_finite_classes : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M] {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), (p : O) ∈ Ideal.span {ϖ} → IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) → ∃ s : Finset (Z1 ρ), ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ) := by
  classical
  intro hT p _ K hK O _ M _ _ _ _ _ _ G _ _ e ρ hρ ϖ hp hN
  set N : Submodule O M := LinearMap.range (LinearMap.lsmul O M ϖ) with hNdef
  have hmemN : ∀ m : M, ϖ • m ∈ N := fun m => ⟨m, rfl⟩
  have hstab : ∀ g : G, N ≤ N.comap (ρ g) := by
    rintro g _ ⟨m, rfl⟩
    show ρ g (ϖ • m) ∈ N
    rw [map_smul]; exact hmemN _
  haveI hdisc : DiscreteTopology (M ⧸ N) :=
    QuotientAddGroup.discreteTopology (N := N.toAddSubgroup) hN
  haveI : CompactSpace (M ⧸ N) :=
    (Submodule.Quotient.mk_surjective N).compactSpace (Submodule.isOpenQuotientMap_mkQ N).continuous
  haveI : Finite (M ⧸ N) := finite_of_compact_of_discrete
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨k, hk1⟩ : ∃ k : ℕ, k = 1 := ⟨1, rfl⟩
  have hkill : ∀ q : M ⧸ N, (p ^ k : ℕ) • q = 0 := by
    intro q
    subst hk1
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have : (p • m : M) = ϖ • (r • m) := by
      rw [← Nat.cast_smul_eq_nsmul O, ← hr, smul_smul, mul_comm]
    rw [this]; exact hmemN _
  haveI : Module (ZMod (p ^ k)) (M ⧸ N) := AddCommGroup.zmodModule (n := p ^ k) hkill
  haveI : ContinuousConstSMul (ZMod (p ^ k)) (M ⧸ N) := ⟨fun _ => continuous_of_discreteTopology⟩
  let f : Formalism.GaloisCohomology.GK p K → Module.End (ZMod (p ^ k)) (M ⧸ N) := fun h =>
    (N.mapQ N (ρ (e.symm h)) (hstab _)).toAddMonoidHom.toZModLinearMap (p ^ k)
  have hf1 : f 1 = 1 := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  have hfm : ∀ a b, f (a * b) = f a * f b := by
    intro a b; refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  let ρ' : Representation (ZMod (p ^ k)) (Formalism.GaloisCohomology.GK p K) (M ⧸ N) := MonoidHom.mk (OneHom.mk f hf1) hfm
  have hρ'mk : ∀ h m, ρ' h (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ (e.symm h) m) := fun h m => rfl
  have hρ' : ContAction ρ' := by
    have hq : Topology.IsQuotientMap (Prod.map (id : Formalism.GaloisCohomology.GK p K → Formalism.GaloisCohomology.GK p K) (N.mkQ)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ N)).isQuotientMap
    show Continuous _
    rw [hq.continuous_iff]
    have : ((fun x : Formalism.GaloisCohomology.GK p K × (M ⧸ N) => ρ' x.1 x.2) ∘ Prod.map id N.mkQ)
        = fun x => Submodule.Quotient.mk (p := N) (ρ (e.symm x.1) x.2) := by
      funext x; rfl
    rw [this]
    exact (Submodule.isOpenQuotientMap_mkQ N).continuous.comp
      (hρ.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK k (M ⧸ N) ρ' (by omega) hρ').1
  let cb : Z1 ρ → (Formalism.GaloisCohomology.GK p K → M ⧸ N) := fun c h => Submodule.Quotient.mk ((c : G → M) (e.symm h))
  have hcb : ∀ c, cb c ∈ Z1 ρ' := by
    intro c
    refine ⟨(Submodule.isOpenQuotientMap_mkQ N).continuous.comp (c.2.1.comp e.symm.continuous), ?_⟩
    intro a b
    simp only [cb, map_mul, c.2.2, Submodule.Quotient.mk_add, hρ'mk]
  let κ : Z1 ρ → H1 ρ' := fun c => Submodule.Quotient.mk ⟨cb c, hcb c⟩
  haveI := Fintype.ofFinite (H1 ρ')
  let pick : H1 ρ' → Z1 ρ := fun y => if hy : ∃ c, κ c = y then hy.choose else 0
  refine ⟨Finset.univ.image pick, fun c => ?_⟩
  have hex : ∃ c', κ c' = κ c := ⟨c, rfl⟩
  have hpick : pick (κ c) = hex.choose := dif_pos hex
  refine ⟨pick (κ c), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  set c₀ := pick (κ c)
  have heq : κ c₀ = κ c := by rw [hpick]; exact hex.choose_spec
  have hB := (Submodule.Quotient.eq _).mp heq.symm
  rw [Submodule.mem_comap] at hB
  obtain ⟨q, hq⟩ := (mem_coboundaries1 ρ' _).mp hB
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
  refine ⟨x, fun g => ?_⟩
  have := hq (e g)
  simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply, cb, hρ'mk,
    MulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply] at this
  rw [← Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.Quotient.mk_sub]
  rw [this]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.VirtualTrace

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def listSum (h : IsPlaceOver A w) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  L.foldr (fun x s => WD.std (x.2.sum s.2)) ⟨0, WDRep.diag h (ι := Fin 0) fun i => i.elim0⟩

theorem mk_listSum_cons (x : Σ n : ℕ, WDRep h (Fin n → ℂ)) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    WD.mk (listSum h (x :: L)).2 = WD.lpSum (WD.mk x.2) (WD.mk (listSum h L).2) := by
  rw [WD.lpSum_mk]
  exact WD.sound (WD.iso_std _).symm

theorem trace_std {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _

theorem trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']

theorem map_lpZero {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) : f (WD.lpZero h) = 1 := by
  have := hf (WD.lpZero h) (WD.lpZero h)
  rw [WD.lpSum_zero] at this
  simpa using this

theorem map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by
  induction L with
  | nil => exact map_lpZero f hf
  | cons x L ih => rw [mk_listSum_cons, hf, ih, List.map_cons, List.prod_cons]

theorem prod_flatMap_replicate {ι α M : Type} [CommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).prod = ∏ i ∈ s, g (x i) ^ n i := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).prod =
      (l.map fun i => g (x i) ^ n i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_replicate, List.prod_replicate]
  rw [key, Finset.prod_map_toList]

theorem sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).sum =
      (l.map fun i => n i • g (x i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih, List.map_replicate, List.sum_replicate]
  rw [key, Finset.sum_map_toList]

end GlobalTheory.WeilDeligne.VirtualTrace

open GlobalTheory.WeilDeligne.VirtualTrace in

theorem GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ),
    (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) →
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ),
    (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) →
    ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  intro E Ω _ _ _ _ _ A w h f hf1 hf2 ι _ d a c hc
  classical
  let x : ι → Σ n : ℕ, WDRep h (Fin n → ℂ) := fun i => ⟨d i, a i⟩
  let L : (ι → ℕ) → List (Σ n : ℕ, WDRep h (Fin n → ℂ)) := fun n =>
    (Finset.univ : Finset ι).toList.flatMap fun i => List.replicate (n i) (x i)
  have hfL : ∀ n, f (WD.mk (listSum h (L n)).2) = ∏ i, f (WD.mk (a i)) ^ n i := fun n => by
    rw [map_listSum f hf1]
    exact prod_flatMap_replicate _ n x (fun y => f (WD.mk y.2))
  have htL : ∀ n σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L n)).2.ρ σ ^ k) =
      ∑ i, (n i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ ^ k) := fun n σ k => by
    rw [trace_listSum]
    rw [sum_flatMap_replicate _ n x (fun y => LinearMap.trace ℂ _ (y.2.ρ σ ^ k))]
    simp only [nsmul_eq_mul, x]
  have hcc : ∀ i, ((c i : ℤ) : ℂ) = (((c i).toNat : ℕ) : ℂ) - (((-c i).toNat : ℕ) : ℂ) := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    push_cast; ring
  have htr : ∀ σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L fun i => (c i).toNat)).2.ρ σ ^ k) =
      LinearMap.trace ℂ _ ((listSum h (L fun i => (-c i).toNat)).2.ρ σ ^ k) := fun σ k => by
    rw [htL, htL, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have := hc (σ ^ k)
    simp only [map_pow, hcc] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPQ : f (WD.mk (listSum h (L fun i => (c i).toNat)).2) =
      f (WD.mk (listSum h (L fun i => (-c i).toNat)).2) :=
    hf2 _ _ fun σ => by
      rw [WD.charPol_mk, WD.charPol_mk]
      exact GlobalTheory.T.charpoly_eq_of_trace_powers _ _ _ _ (htr σ)
  rw [hfL, hfL] at hPQ
  have hz : ∀ i, f (WD.mk (a i)) ^ c i =
      f (WD.mk (a i)) ^ (c i).toNat * (f (WD.mk (a i)) ^ (-c i).toNat)⁻¹ := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hPQ, mul_inv_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjection
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Fibre

variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

theorem inf_ker_snd_eq (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    Submodule.mem_comap, LinearMap.inl_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hx, rfl⟩

theorem isLat_of_comap_inl_map_snd {M : Submodule O (A₁ × A₂)}
    (h₁ : IsLat O E (M.comap (LinearMap.inl O A₁ A₂)))
    (h₂ : IsLat O E (M.map (LinearMap.snd O A₁ A₂))) : IsLat O E M := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd O A₁ A₂) h₂.1 ?_, ?_⟩
  · rw [inf_ker_snd_eq]; exact h₁.1.map _
  · set S := Submodule.span E (M : Set (A₁ × A₂)) with hS
    have hl : LinearMap.range (LinearMap.inl E A₁ A₂) ≤ S := by
      rw [LinearMap.range_eq_map, ← h₁.2, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (by simpa using hx)
    have hr : S.map (LinearMap.snd E A₁ A₂) = ⊤ := by
      rw [hS, Submodule.map_span, ← h₂.2]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd E A₁ A₂) := by rw [hr]; trivial
    obtain ⟨z, hz, hzb⟩ := hb
    have hab : ((a, b) : A₁ × A₂) = z + LinearMap.inl E A₁ A₂ (a - z.1) := by
      ext <;> simp [← hzb]
    rw [hab]
    exact S.add_mem hz (hl ⟨_, rfl⟩)

end Fibre

theorem ncard_fibre_latProj (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) :
    resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 →
      ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) =
        (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^
          val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro hR y
  have key := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hR y.1.1 y.2.1 y.1.2.1 y.2.2.1 y.1.2.2 y.2.2.2
  let e : ↥(latProj O E g₁ g₂ ⁻¹' {y}) ≃
      {M : Submodule O (A₁ × A₂) // (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧ M.map (LinearMap.snd O A₁ A₂) = y.2.1} :=
    { toFun := fun M => ⟨M.1.1, M.1.2.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.1 : Submodule O A₁)) M.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.2 : Submodule O A₂)) M.2⟩
      invFun := fun M => ⟨⟨M.1, isLat_of_comap_inl_map_snd (by rw [M.2.2.1]; exact y.1.2.1)
          (by rw [M.2.2.2]; exact y.2.2.1), M.2.1⟩,
        Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext M.2.2.1) (Subtype.ext M.2.2.2))⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  have hc : (latProj O E g₁ g₂ ⁻¹' {y}).ncard = Nat.card {M : Submodule O (A₁ × A₂) //
      (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧
        M.map (LinearMap.snd O A₁ A₂) = y.2.1} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  rw [hc]
  exact key

end GlobalTheory.UnitLemma
end
end

