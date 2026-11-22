import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeNefAboveSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeSubvarSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeBundleSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLocalizeNefAbove
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

theorem LocalizeNefAbove.proof (h₁ : LocalizeSubvar.Statement) (h₂ : LocalizeRestrLen.Statement) :
    LocalizeNefAbove.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M hM pp' hJ hpp'
  have hJp : 𝔪.map (C : S →+* Poly S N) ≤
      pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N) := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    change MvPolynomial.map (algebraMap S O) (C m) ∈ pp'
    rw [map_C]
    exact hJ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hm))
  have hL : (![M.baseChange O] : Fin 1 → SubSystem O x Ω) = fun i => (![M] i).baseChange O := by
    funext i; fin_cases i; rfl
  have key : interNum pp' ![M.baseChange O] =
      interNum (pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N)) ![M] := by
    unfold interNum
    congr 1
    funext c
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    rw [hL, baseChange_tensorSub, ← baseChange_twistSys (S := S), ← baseChange_twist]
    exact h₂ S 𝔪 O Ω N x pp' hJ _
  rw [key]
  exact hM _ hJp (h₁ S 𝔪 O Ω N x pp' 1 hJ hpp')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLocalizeRestrLen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

theorem LocalizeRestrLen.proof : LocalizeRestrLen.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x pp' hpp' F
  set p := pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N) with hp_def
  set G := F.twist (idealSys x p) with hG_def
  have hG : (F.baseChange O).twist (idealSys x pp') = G.baseChange O := by
    rw [idealSys_localize 𝔪 pp', hG_def, baseChange_twist]
  have hCO : ∀ m ∈ 𝔪, C (algebraMap S O m) ∈ pp' := fun m hm =>
    hpp' (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hm))
  have hCS : ∀ m ∈ 𝔪, C m ∈ p := fun m hm => by
    rw [hp_def, Ideal.mem_comap]
    change MvPolynomial.map (algebraMap S O) (C m) ∈ pp'
    rw [map_C]
    exact hCO m hm
  have killS : ∀ m ∈ 𝔪, ∀ y ∈ F.secs, algebraMap S Ω m * y ∈ G.secs := fun m hm y hy =>
    mul_mem_secs_twist_idealSys p (hCS m hm) F hy
  have killO : ∀ m ∈ 𝔪, ∀ y ∈ (F.baseChange O).secs, algebraMap S Ω m * y ∈ (G.baseChange O).secs := by
    intro m hm y hy
    rw [← hG, IsScalarTower.algebraMap_apply S O Ω]
    exact mul_mem_secs_twist_idealSys pp' (hCO m hm) _ hy
  unfold restrLen
  rw [hG]
  let P' := ((G.baseChange O).secs).comap (F.baseChange O).secs.subtype
  let φ : F.secs →ₗ[S] ((F.baseChange O).secs ⧸ P') :=
    { toFun := fun y => Submodule.Quotient.mk ⟨(y : Ω), mem_secs_baseChange y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker φ = G.secs.comap F.secs.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    change y ∈ (G.baseChange O).secs ↔ y ∈ G.secs
    constructor
    · intro h
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_secs 𝔪 h
      obtain ⟨u, i, hi, hui⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
      have h1 : algebraMap S Ω u * algebraMap S Ω t + algebraMap S Ω i = 1 := by
        rw [← map_mul, ← map_add, hui, map_one]
      have e : y = algebraMap S Ω u * (algebraMap S Ω t * y) + algebraMap S Ω i * y := by
        linear_combination (-y) * h1
      rw [e]
      refine add_mem ?_ (killS i hi y hy)
      rw [← Algebra.smul_def]
      exact G.secs.smul_mem u hty
    · exact fun h => mem_secs_baseChange h
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨t, ht, htw⟩ := exists_mul_mem_secs 𝔪 hw
    obtain ⟨u, i, hi, hui⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
    have h1 : algebraMap S Ω u * algebraMap S Ω t + algebraMap S Ω i = 1 := by
      rw [← map_mul, ← map_add, hui, map_one]
    refine ⟨u • ⟨_, htw⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change u • (algebraMap S Ω t * w) - w ∈ (G.baseChange O).secs
    have e : u • (algebraMap S Ω t * w) - w = -(algebraMap S Ω i * w) := by
      rw [Algebra.smul_def]
      linear_combination w * h1
    rw [e]
    exact neg_mem (killO i hi w hw)
  have hkill : ∀ m ∈ 𝔪, ∀ q : (F.baseChange O).secs ⧸ P', m • q = 0 := by
    intro m hm q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change m • (w : Ω) ∈ (G.baseChange O).secs
    rw [Algebra.smul_def]
    exact killO m hm w w.2
  rw [← length_eq_of_killed 𝔪 hkill,
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)).length_eq]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapCEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (i : ℕ) : Cochain G i ≃ₗ[R] Cochain G' i :=
  LinearEquiv.piCongrRight fun I : Idx U i => e I.1

theorem mapCEquiv_d (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : mapCEquiv e (i + 1) (d G ρ i s) = d G' ρ' i (mapCEquiv e i s) :=
  mapC_d (fun I => (e I).toLinearMap) he i s

theorem mem_bdry_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ bdry G ρ i ↔ mapCEquiv e i s ∈ bdry G' ρ' i := by
  cases i with
  | zero =>
    change s ∈ (⊥ : Submodule R _) ↔ mapCEquiv e 0 s ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  | succ i =>
    change s ∈ LinearMap.range (d G ρ i) ↔ mapCEquiv e (i + 1) s ∈ LinearMap.range (d G' ρ' i)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨mapCEquiv e i t, (mapCEquiv_d e he i t).symm⟩
    · rintro ⟨t', ht'⟩
      refine ⟨(mapCEquiv e i).symm t', (mapCEquiv e (i + 1)).injective ?_⟩
      rw [mapCEquiv_d e he, LinearEquiv.apply_symm_apply, ht']

theorem mem_ker_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ LinearMap.ker (d G ρ i) ↔ mapCEquiv e i s ∈ LinearMap.ker (d G' ρ' i) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← mapCEquiv_d e he, LinearEquiv.map_eq_zero_iff]

def kerEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G' ρ' i) :=
  LinearEquiv.ofSubmodules (mapCEquiv e i) _ _ (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_iff e he,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

def equivH (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  Submodule.Quotient.equiv _ _ (kerEquiv e he i) (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, mem_bdry_iff e he]
    congr! 1
    change mapCEquiv e i ((mapCEquiv e i).symm (z : Cochain G' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

end Cech

section Mul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

def mulSubMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) (I : Chart x) : F₁.sub I →ₗ[k] G₁.sub I where
  toFun y := ⟨s * y, h₁ I y y.2⟩
  map_add' a b := Subtype.ext (mul_add s (a : Ω) b)
  map_smul' c y := Subtype.ext (by
    change s * ((c • y : F₁.sub I) : Ω) = ((c • (⟨s * y, h₁ I y y.2⟩ : G₁.sub I) : G₁.sub I) : Ω)
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, mul_smul_comm])

def mulQuotMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mapQ (SubSystem.quotSub G₁ G₂ I) (mulSubMap h₁ I)
    (fun y hy => (h₃ I y y.2).mpr hy)

theorem mulQuotMap_bijective (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz

end Mul

theorem MulQuotEq.proof : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefGenericLocalize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem isUnit_algebraMap_primeCompl {S : Type} [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] {K : Type} [Field K]
    [Algebra S K] (h : Function.Injective (algebraMap S K)) (y : 𝔪.primeCompl) : IsUnit (algebraMap S K y) :=
  IsUnit.mk0 _ fun h' => y.2 (by rw [(map_eq_zero_iff _ h).mp h']; exact 𝔪.zero_mem)

theorem NefGenericLocalize.proof (hI : NefExtendIso.Statement) (hB : LocalizeBundle.Statement)
    (hN : LocalizeNefAbove.Statement) : NefGenericLocalize.Statement := by
  intro hD S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM
  by_cases h0 : 𝔪 = ⊥
  · subst h0
    refine hI S F Ω N x M.toSubSystem
      ⟨IsFractionRing.injective S F, IsFractionRing.surjective_iff_isField.mpr (Ring.isField_iff_maximal_bot.mpr h𝔪)⟩ ?_
    rw [Ideal.map_bot] at hM
    exact hM
  · have hinj : Function.Injective (algebraMap S Ω) := by
      rw [IsScalarTower.algebraMap_eq S F Ω]
      exact (algebraMap F Ω).injective.comp (IsFractionRing.injective S F)
    let O := Localization.AtPrime 𝔪
    let _ : Algebra O Ω :=
      (IsLocalization.lift (M := 𝔪.primeCompl) (S := O) (isUnit_algebraMap_primeCompl 𝔪 hinj)).toAlgebra
    let _ : Algebra O F := (IsLocalization.lift (M := 𝔪.primeCompl) (S := O)
      (isUnit_algebraMap_primeCompl 𝔪 (IsFractionRing.injective S F))).toAlgebra
    have : IsScalarTower S O Ω := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
    have : IsScalarTower S O F := IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
    have : IsScalarTower O F Ω := IsScalarTower.of_algebraMap_eq' <|
      IsLocalization.ringHom_ext 𝔪.primeCompl <| by
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
          ← IsScalarTower.algebraMap_eq]
    have : IsFractionRing O F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl O F
    have : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S h0 O
    obtain ⟨M', hM'⟩ := hB S 𝔪 O Ω N x M
    have hN' := hN S 𝔪 O Ω N x M.toSubSystem hM
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 O, ← hM'] at hN'
    convert hD O F Ω N x M' hN' using 1
    refine Kleiman.SubSystem.ext_sub fun I => ?_
    change Submodule.span (Kleiman.chartRing F x I) (M.sub I : Set Ω) =
      Submodule.span (Kleiman.chartRing F x I) (M'.sub I : Set Ω)
    rw [show M'.sub I = (M.toSubSystem.baseChange O).sub I by rw [← hM']]
    exact (Kleiman.span_extend_span I _).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_single (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by
  have hf : List.finRange 1 = [0] := rfl
  split_ifs with h
  · simp [tensorSub, hf, h, twistSys_zero_twist]
  · simp [tensorSub, hf, h]

end Helpers

theorem NefRestrict.proof (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionNonvanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem SectionNonvanish.proof : SectionNonvanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp _ hle ⟨i, hi⟩ D hD
  have hxi : x i ≠ 0 := fun h0 =>
    hi (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).mpr (by rw [aeval_X, h0])))
  refine not_forall_not.mp fun hcon => ?_
  let I : Chart x := singleChart hxi
  have hsec : ∀ s ∈ D.toSubSystem.secs, s ∈ idealMod pp I * D.toSubSystem.sub I := by
    intro s hs
    by_contra hs'
    refine hcon s ⟨hs, I, ?_⟩
    rwa [SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨P, hP⟩ := D.invertible I
  have hsub : D.toSubSystem.sub I ≤ idealMod pp I * D.toSubSystem.sub I := by
    rw [← hD I, Submodule.span_le]
    intro s hs
    rw [hD I]
    exact hsec s hs
  have hone : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I :=
    calc (1 : Submodule (chartRing k x I) Ω) = D.toSubSystem.sub I * P := hP.symm
      _ ≤ idealMod pp I * D.toSubSystem.sub I * P := mul_le_mul' hsub le_rfl
      _ = idealMod pp I := by rw [mul_assoc]; erw [hP]; rw [mul_one]
  have h1 : (1 : Ω) ∈ idealMod pp I := hone (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  refine SectionCount.Drop.Term.one_not_mem_idealMod hpp hle (I := I) (fun j hj => ?_) h1
  obtain rfl : j = i := Finset.mem_singleton.mp hj
  exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnW
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

