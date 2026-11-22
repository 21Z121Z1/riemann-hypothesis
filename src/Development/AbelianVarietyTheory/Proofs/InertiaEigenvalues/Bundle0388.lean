import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.JointDiag

theorem aeval_restrict_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) (y : W) :
    ((aeval (T.restrict hW) q y : W) : V) = aeval T q (y : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      LinearMap.restrict_apply, Submodule.coe_smul]
    rw [Module.End.pow_restrict n hW]
    rfl

theorem ker_prod {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⨆ r ∈ s, f.eigenspace r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))

theorem iSup_eigenspace_eq_top_of_aeval {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (p : K[X]) (hs : p.Separable) (hp : p.Splits) (h0 : aeval f p = 0) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  classical
  have hne : p ≠ 0 := hs.ne_zero
  let s : Finset K := ⟨p.roots, nodup_roots hs⟩
  have hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod := rfl
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := LinearMap.congr_fun h0 x
    rw [hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.resolve_left hc
  rw [ker_prod] at hker
  rw [eq_top_iff, ← hker]
  exact iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r

theorem le_iSup_jointEigenspace_inf : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) (W : Submodule K V), (∀ a c, Commute (T a) (T c)) → (∀ a, ∀ x ∈ W, T a x ∈ W) → (∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ ∀ x ∈ W, Polynomial.aeval (T a) p x = 0) → W ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
  intro K V ι _ _ _ _ T W hc hW hp
  let S : ι → Module.End K W := fun a => (T a).restrict (hW a)
  have hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0 := by
    intro a
    obtain ⟨p, hs, hsp, hx⟩ := hp a
    refine ⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [aeval_restrict_coe]
    simpa using hx y y.2
  have hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ := by
    intro a μ
    obtain ⟨p, hs, _, h0⟩ := hS0 a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤ := by
    intro a
    obtain ⟨p, hs, hsp, h0⟩ := hS0 a
    simp_rw [hmax]
    exact iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0
  have hcomm : Pairwise fun i j => Commute (S i) (S j) := fun i j _ =>
    LinearMap.restrict_commute (hc i j) (hW i) (hW j)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag
  simp_rw [hmax] at htop
  have hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤
      ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [SetLike.mem_coe] at hy ⊢
    rw [Submodule.mem_iInf]
    intro a
    have h := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)
    have h' := congrArg Subtype.val h
    simp only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'
    rw [LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, h', sub_self]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a) := by
    rw [htop]; trivial
  exact hle ⟨⟨x, hx⟩, hmem, rfl⟩

end GlobalTheory.JointDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexDvdClassNumber
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UnramHom

section Algebra

variable {O M G Γ : Type} [CommRing O] [AddCommGroup M] [Module O M] [Group G] [CommGroup Γ]

def asHom (f : G → M) (hf : ∀ a b, f (a * b) = f a + f b) : G →* Multiplicative M :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => by rw [hf, ofAdd_add]

theorem length_le {l : ℕ} (hl : l.Prime) (hu : ∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : O)) (L : ℕ∞)
    (hL : Module.length O (Submodule.torsionBy O M (l : O)) ≤ L) (π : G →* Γ) (hπ : Function.Surjective π) (n : ℕ) :
    n ≠ 0 → ∀ N : Subgroup Γ, N.index = n → ∀ C : Submodule O (G → M), (∀ f ∈ C, ∀ a b, f (a * b) = f a + f b) →
      (∀ f ∈ C, ∀ a, π a ∈ N → f a = 0) → Module.length O C ≤ L * (padicValNat l n : ℕ∞) := by
  have := Fact.mk hl
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn N hN C hadd hker
  by_cases h1 : n = 1
  · have hT : N = ⊤ := Subgroup.index_eq_one.1 (hN.trans h1)
    have : C = ⊥ := (Submodule.eq_bot_iff _).2 fun f hf => funext fun a => hker f hf a (hT ▸ trivial)
    subst this
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have := Fact.mk hp
  have : N.FiniteIndex := ⟨hN ▸ hn⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Γ ⧸ N) p (hN ▸ hpn :)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := hπ y
  let N' : Subgroup Γ := (Subgroup.zpowers (π a : Γ ⧸ N)).comap (QuotientGroup.mk' N)
  have hi : p * N'.index = n := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), ← hx, ← Nat.card_zpowers,
      Subgroup.card_mul_index, ← hN]
    rfl
  have hi0 : N'.index ≠ 0 := fun h => hn (by rw [← hi, h, mul_zero])
  have hlt : N'.index < n := by
    rw [← hi]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hi0) hp.one_lt
  let ev : C →ₗ[O] M := (LinearMap.proj a).comp C.subtype
  let C' : Submodule O (G → M) := (LinearMap.ker ev).map C.subtype
  have hC' := ih _ hlt hi0 N' rfl C' (by rintro _ ⟨f, -, rfl⟩; exact hadd f f.2) (by
    rintro _ ⟨f, hf, rfl⟩ b ⟨k, hk⟩
    have hf' : asHom f.1 (hadd f f.2) a = 1 := congrArg Multiplicative.ofAdd (LinearMap.mem_ker.1 hf)
    have h2 : π ((a ^ k)⁻¹ * b) ∈ N := by
      rw [map_mul, map_inv, map_zpow]
      exact QuotientGroup.eq.1 hk
    have h3 : asHom f.1 (hadd f f.2) ((a ^ k)⁻¹ * b) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_mul, map_inv, map_zpow, hf', one_zpow, inv_one, one_mul] at h3
    exact congrArg Multiplicative.toAdd h3)
  have hk : Module.length O (LinearMap.ker ev) = Module.length O C' :=
    (Submodule.equivMapOfInjective _ C.injective_subtype _).length_eq
  have hr : LinearMap.range ev ≤ Submodule.torsionBy O M (p : O) := by
    rintro _ ⟨f, rfl⟩
    have h2 : π (a ^ p) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, map_pow, QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
    have h3 : asHom f.1 (hadd f f.2) (a ^ p) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_pow] at h3
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    exact congrArg Multiplicative.toAdd h3
  have hsum : Module.length O C = Module.length O (LinearMap.ker ev) + Module.length O (LinearMap.range ev) :=
    Module.length_eq_add_of_exact (LinearMap.ker ev).subtype ev.rangeRestrict (Submodule.injective_subtype _)
      ev.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have hr' := Module.length_le_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
  rw [hsum, hk, ← hi, padicValNat.mul hp.ne_zero hi0, Nat.cast_add, mul_add, add_comm (L * _)]
  refine add_le_add hC' (hr'.trans ?_)
  by_cases hpl : p = l
  · subst hpl
    rwa [padicValNat_self, Nat.cast_one, mul_one]
  · have : Submodule.torsionBy O M (p : O) = ⊥ := (Submodule.eq_bot_iff _).2 fun m hm =>
      ((hu p hp hpl).smul_eq_zero).1 ((Submodule.mem_torsionBy_iff _ _).1 hm)
    rw [this]
    simp

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] {a : O} (ha : a ≠ 0) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  let u : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
  have hu : a • u = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun _ => 1, funext fun j => ?_⟩
    simp [Algebra.smul_def, ha']
  let g : (O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O 1) a :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton O _ ⟨u, hu⟩) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hu)
  refine Module.length_le_of_surjective g ?_
  rintro ⟨m, hm⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨Submodule.Quotient.mk (c 0), Subtype.ext ?_⟩
  show c 0 • u = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h0 : algebraMap O (FractionRing O) (c 0) = a • x 0 := congrFun hc 0
  rw [Pi.smul_apply, Algebra.smul_def, h0, Algebra.smul_def]
  field_simp

end Algebra

section Galois

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.HeckeGal GlobalTheory.Mem.UnitIndex Filter

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem eq_one_of_class [IsTotallyComplex E] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {B : Type} [CommGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (A : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v)
    (hI : ∀ v, ∀ σ ∈ Ine (F := E) (A v), φ σ = 1) (σ : G E Ω)
    (hσ : toAb E Ω σ ∈ (classHom E).ker.map art) : φ σ = 1 := by
  obtain ⟨x, hx, e⟩ := hσ
  let ψ : Ideles E →* B := (liftAb φ hφ).comp art
  have hψ : Continuous ψ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (ψ.ker : Set (Ideles E)) := (isOpen_discrete {1}).preimage hψ
  have hfin : Finite ψ.range := by
    refine ((isCompact_range hφ).finite_of_discrete.subset ?_).to_subtype
    rintro _ ⟨y, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art y)
    exact ⟨τ, by rw [MonoidHom.comp_apply, ← hτ, liftAb_toAb]⟩
  have hu : ∀ v x, IsUnitAt v x → ψ (localIdele E v x) = 1 := fun v y hy => by
    obtain ⟨τ, hτ, e⟩ := (ha.ine v (A v) (hA v) _).1 ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply, ← e, liftAb_toAb, hI v τ hτ]
  have hle : unitIdl E ⊔ (diagUnits E).range ≤ ψ.ker := by
    refine sup_le (fun b hb => ?_) ?_
    · have e1 : ψ (finPartI E b) = ψ b := congrArg Subtype.val (GlobalTheory.RingCls.map_finPartI ψ.rangeRestrict b)
      rw [MonoidHom.mem_ker, ← e1]
      refine (ψ.ker.isClosed_of_isOpen ho).mem_of_tendsto
        (GlobalTheory.Mem.LocTriv.tendsto_part (finPartI_mem_unitIdl.2 hb) fun _ => rfl) (Eventually.of_forall fun S => ?_)
      refine Subgroup.prod_mem _ fun v _ => ?_
      exact hu v _ (hb v)
    · rintro _ ⟨k, rfl⟩
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have := MonoidHom.mem_ker.1 (hle (ker_classHom_le E hx))
  rwa [MonoidHom.comp_apply, e, liftAb_toAb] at this

omit [IsAlgClosure E Ω] in

theorem index_dvd_classNumber {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ((classHom E).ker.map art).index ∣ classNumber E := by
  refine (Subgroup.index_map_dvd _ ha.quot.surjective).trans ?_
  rw [Subgroup.index_ker, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

end Galois

theorem wkg_one (D : D7) (i : D.nd.Loc) (g : GE D.nd) (m : KOG (D.nd.O i) 1) :
    WKG (chiRatO D.nd i 1) g m = m := by
  have h : chiRatO D.nd i 1 g = chiRatO D.nd i 1 1 := by
    rw [map_one]
    simp [chiRatO, twistM]
  have h2 : WKG (chiRatO D.nd i 1) g = WKG (chiRatO D.nd i 1) 1 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    exact congrArg (fun X : Matrix (Fin 1) (Fin 1) (D.nd.O i) => (Submodule.Quotient.mk
      (Matrix.toLinAlgEquiv' (X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) x) : KOG (D.nd.O i) 1)) h
  rw [h2, map_one]
  rfl

theorem length_le_classNumber : GlobalTheory.Published.GlobalArtinReciprocity →
    ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)),
      C ≤ Z1 (WKG (chiRatO D.nd i 1)) → (∀ v, resIne i C v = ⊥) →
      Module.length (D.nd.O i) ↥C ≤
        lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) := by
  intro H D i C hC hres
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := H D.host.E D.nd.Om
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hadd : ∀ f ∈ C, ∀ a b, f (a * b) = f a + f b := fun f hf a b => by
    rw [(hC hf).2, wkg_one]
  have hl0 : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
    rw [map_natCast, map_zero, ← map_natCast (D.nd.embK i), map_eq_zero] at h1
    exact hl.ne_zero (Nat.cast_eq_zero.1 h1)
  have hu : ∀ p : ℕ, p.Prime → p ≠ D.nd.l i → IsUnit (p : D.nd.O i) := fun p hp hpl => by
    have h1 : IsUnit (p : ℤ_[D.nd.l i]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hl hp).2 hpl.symm))
    simpa using h1.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  have hd := index_dvd_classNumber ha
  have hh : classNumber D.host.E ≠ 0 := classNumber_ne_zero _
  refine (length_le hl hu _ (length_torsionBy_le hl0) (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
    GlobalTheory.HeckeGal.toAb_surjective _ (ne_zero_of_dvd_ne_zero hh hd) _ rfl C hadd fun f hf σ hσ => ?_).trans ?_
  · refine congrArg Multiplicative.toAdd (eq_one_of_class ha (asHom f (hadd f hf)) (hC hf).1 D.nd.plOm.1 D.nd.plOm.2
      (fun v τ hτ => ?_) σ hσ)
    have h1 : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) 1) Subtype.val f ∈ resIne i C v := ⟨f, hf, rfl⟩
    rw [hres v, Submodule.mem_bot] at h1
    exact congrArg Multiplicative.ofAdd (congrFun h1 ⟨τ, hτ⟩)
  · refine mul_le_mul_right (Nat.cast_le.2 ?_) _
    exact (padicValNat_dvd_iff_le hh).1 (pow_padicValNat_dvd.trans hd)

end GlobalTheory.UnramHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducesWAndExistsEmb
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem ideal_dual_symm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (x y : ↥I) : f x * (y : A) = f y * (x : A) := by
  have h : (x : A) • y = (y : A) • x := Subtype.ext (by simp [mul_comm])
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm (f x), ← this, mul_comm]

theorem invertible_ideal_eq_of_not_le_maximal_mul (A : Type) [CommRing A] (I N : Ideal A) :
    Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  intro hI hNI hm

  set c : Ideal A := N.colon I with hc
  have key : ∀ (f : Module.Dual A ↥I) (n : ↥I), (n : A) ∈ N → f n ∈ c := by
    intro f n hn
    rw [hc, Submodule.mem_colon]
    intro p hp
    rw [smul_eq_mul, ideal_dual_symm I f n ⟨p, hp⟩]
    exact N.mul_mem_left _ hn
  have hcTop : c = ⊤ := by
    by_contra hne
    obtain ⟨m, hmax, hcm⟩ := Ideal.exists_le_maximal c hne
    apply hm m hmax
    intro n hn
    obtain ⟨t, ht⟩ := hI.bijective.2 1
    have hall : ∀ t : Module.Dual A ↥I ⊗[A] ↥I, contractLeft A ↥I t * n ∈ m * I := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [contractLeft_apply, ideal_dual_symm I f x ⟨n, hNI hn⟩]
        exact Ideal.mul_mem_mul (hcm (key f ⟨n, hNI hn⟩ hn)) x.2
      | add s u hs hu => rw [map_add, add_mul]; exact Ideal.add_mem _ hs hu
    simpa [ht] using hall t
  apply le_antisymm hNI
  intro y hy
  have h1 : (1 : A) ∈ c := hcTop ▸ Submodule.mem_top
  rw [hc, Submodule.mem_colon] at h1
  simpa using h1 y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealPrincipalOnZariskiCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | zero => simp
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal

open GlobalTheory.BSP.ZarPrincipal in

theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalizedFractionSemilinearTransition
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrac_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  intro A A' _ _ k N _ _ N' _ _ τ t t' a y y' z m z' n i j h1 h2 h3 h4 h5
  unfold IsFrac at h1 h2 h3 h4
  obtain ⟨⟨_, r₁, rfl⟩, e1⟩ := LocalizedModule.mk_eq.1 (h1.symm.trans h2)
  obtain ⟨⟨_, r₂, rfl⟩, e2⟩ := LocalizedModule.mk_eq.1 (h3.symm.trans h4)
  simp only [Submonoid.smul_def] at e1 e2
  have e3 := congrArg τ e1
  simp only [map_smulₛₗ, map_pow] at e3
  refine ⟨r₁ + r₂ + a, ?_⟩
  linear_combination (norm := skip) (-(k t ^ r₂ * t' ^ (r₁ + r₂ + a) * t' ^ j)) • e3
    + (k t ^ (r₂ + r₁ + i) * t' ^ (r₁ + r₂ + j)) • h5
    + (k t ^ (r₁ + r₂ + a + i) * t' ^ r₁) • e2
  match_scalars <;> ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  first | exact @GlobalTheory.BSP.isPrincipalIdealRing_away_l | exact GlobalTheory.BSP.isPrincipalIdealRing_away_l | (intros; apply GlobalTheory.BSP.isPrincipalIdealRing_away_l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_conductor_exponent : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  first | exact @GlobalTheory.LamTie.lam0_expAt | exact GlobalTheory.LamTie.lam0_expAt | (intros; apply GlobalTheory.LamTie.lam0_expAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  first | exact @GlobalTheory.tate_double_annihilator | exact GlobalTheory.tate_double_annihilator | (intros; apply GlobalTheory.tate_double_annihilator <;> assumption)
end

