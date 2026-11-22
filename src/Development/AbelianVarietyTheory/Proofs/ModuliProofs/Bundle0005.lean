import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdMulOfIdem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupOfFinite
section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.LevQuot

variable {X Y : Scheme.{0}}

theorem isOpenImmersion_graph (r : X ⟶ Y) [Etale r] (f : X ⟶ X) (h : 𝟙 X ≫ r = f ≫ r) :
    IsOpenImmersion (pullback.lift (𝟙 X) f h) := by
  have hpost : (@IsOpenImmersion : MorphismProperty Scheme.{0}).HasOfPostcompProperty
      (@Etale : MorphismProperty Scheme.{0}) := by
    refine MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr ?_
    intro A B u hu
    have : Etale u := hu
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal u))
  have hsec : IsOpenImmersion (pullback.lift (𝟙 X) f h ≫ pullback.fst r r) := by
    rw [pullback.lift_fst]
    infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) _ (pullback.fst r r)
    (inferInstance : Etale (pullback.fst r r)) hsec

theorem appLE_congr_hom {Z : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  simp only [e]

theorem exists_geomPoint (Z : Scheme.{0}) (z : Z) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k)
    (w : Spec (CommRingCat.of k) ⟶ Z) (p : Spec (CommRingCat.of k)), w p = z := by
  let K := AlgebraicClosure (Z.residueField z)
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z, p, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem invariant_descends (r : X ⟶ Y) [Etale r] [QuasiCompact r] [Surjective r] {Γ : Type} (ρ : Γ → (X ⟶ X))
    (hρ : ∀ g, ρ g ≫ r = r)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Spec (CommRingCat.of k) ⟶ X), y ≫ r = y' ≫ r →
      ∃ g, y' = y ≫ ρ g) (V : Y.Opens) :
    Function.Injective (r.app V).hom ∧ ∀ f : Γ(X, r ⁻¹ᵁ V),
      (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom := by
  have hcond : ∀ g, 𝟙 X ≫ r = ρ g ≫ r := fun g => by rw [Category.id_comp, hρ g]
  have hpb := IsPullback.of_hasPullback r r
  have hsame : ∀ x : ↥(pullback r r), r (pullback.snd r r x) = r (pullback.fst r r x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hgW : pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V ≤ pullback.snd r r ⁻¹ᵁ r ⁻¹ᵁ V := fun x hx => by
    change r (pullback.snd r r x) ∈ V
    rw [hsame]
    exact hx
  have hinvle : ∀ g, r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V) := fun g y hy => by
    change r (ρ g y) ∈ V
    rw [← Scheme.Hom.comp_apply, hρ g]
    exact hy
  have key := fun s => GlobalTheory.FlatDescent.existsUnique_app_eq_iff r hpb V
    (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) rfl le_rfl hgW s
  have hcompat : r.app V ≫ (pullback.fst r r).appLE _ _ le_rfl =
      r.app V ≫ (pullback.snd r r).appLE _ _ hgW :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans
      ((appLE_congr_hom pullback.condition _ _ _ _).trans (Scheme.Hom.comp_appLE _ _ _ _ _))
  constructor
  · intro a b hab
    obtain ⟨c, -, huniq⟩ := (key ((r.app V).hom a)).mpr (congrArg (fun φ => φ.hom a) hcompat)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  · intro f hinv
    refine ExistsUnique.exists ((key f).mpr ?_)
    apply TopCat.Presheaf.section_ext (pullback r r).sheaf
    intro x hx
    obtain ⟨k, _, _, w, pt, hw⟩ := exists_geomPoint (pullback r r) x
    obtain ⟨g, hg⟩ := htr k (w ≫ pullback.fst r r) (w ≫ pullback.snd r r)
      (by simp only [Category.assoc, pullback.condition])
    obtain ⟨ι, hιfst, hιsnd, hιop⟩ : ∃ ι : X ⟶ pullback r r,
        ι ≫ pullback.fst r r = 𝟙 X ∧ ι ≫ pullback.snd r r = ρ g ∧ IsOpenImmersion ι :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, isOpenImmersion_graph r (ρ g) (hcond g)⟩
    have hwι : w = (w ≫ pullback.fst r r) ≫ ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιfst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, hιsnd, hg, Category.assoc]
    have hxι : x = ι ((w ≫ pullback.fst r r) pt) := by
      rw [← Scheme.Hom.comp_apply, ← hwι, hw]
    subst hxι
    have hfi : ∀ y, pullback.fst r r (ι y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, hιfst]
      rfl
    have hle : ι ⁻¹ᵁ (pullback.fst r r ⁻¹ᵁ r ⁻¹ᵁ V) ≤ r ⁻¹ᵁ V := fun y hy => by
      change r (pullback.fst r r (ι y)) ∈ V at hy
      rw [hfi] at hy
      exact hy
    have e1 : (pullback.fst r r).appLE (r ⁻¹ᵁ V) _ le_rfl ≫ ι.app _ =
        X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hιfst _ _ _ hle]
      dsimp only [Scheme.Hom.appLE]
      rw [Scheme.Hom.id_app]
      exact Category.id_comp _
    have e2 : (pullback.snd r r).appLE (r ⁻¹ᵁ V) _ hgW ≫ ι.app _ =
        (ρ g).appLE (r ⁻¹ᵁ V) (r ⁻¹ᵁ V) (hinvle g) ≫ X.presheaf.map (homOfLE hle).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom hιsnd _ _ _ (hle.trans (hinvle g)), Scheme.Hom.appLE_map]
    apply (ConcreteCategory.bijective_of_isIso (ι.stalkMap _)).1
    erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    have h1 := congrArg (fun φ => φ.hom f) e1
    have h2 := congrArg (fun φ => φ.hom f) e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
    rw [hinv g (hinvle g)] at h2
    exact h1.trans h2.symm

def autOver (r : X ⟶ Y) : Subgroup (Aut X) where
  carrier := {ρ | ρ.hom ≫ r = r}
  mul_mem' := fun {a b} ha hb => by
    show (b.hom ≫ a.hom) ≫ r = r
    rw [Category.assoc, ha, hb]
  one_mem' := Category.id_comp _
  inv_mem' := fun {a} ha => by
    show a.inv ≫ r = r
    exact (Iso.inv_comp_eq a).2 (Eq.symm ha)

theorem exists_liftAut {P Q : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ X} {q : Q ⟶ Y} {r : X ⟶ Y} (h : IsPullback φ p q r) :
    ∃ τ : autOver r →* Aut P, ∀ ω, (τ ω).hom ≫ φ = φ ∧ (τ ω).hom ≫ p = p ≫ ω.1.hom := by
  have hom_r : ∀ ω : autOver r, ω.1.hom ≫ r = r := fun ω => ω.2
  have inv_r : ∀ ω : autOver r, ω.1.inv ≫ r = r := fun ω => (Iso.inv_comp_eq ω.1).2 (hom_r ω).symm
  have sq : ∀ u : X ⟶ X, u ≫ r = r → φ ≫ q = (p ≫ u) ≫ r := fun u hu => by
    rw [Category.assoc, hu, h.w]
  have back : ∀ (u v : X ⟶ X) (hu : u ≫ r = r) (hv : v ≫ r = r), u ≫ v = 𝟙 X →
      h.lift φ (p ≫ u) (sq u hu) ≫ h.lift φ (p ≫ v) (sq v hv) = 𝟙 P := fun u v hu hv huv => by
    apply h.hom_ext
    · simp
    · simp only [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc, huv, Category.comp_id,
        Category.id_comp]
  let lift1 : autOver r → Aut P := fun ω =>
    { hom := h.lift φ (p ≫ ω.1.hom) (sq _ (hom_r ω))
      inv := h.lift φ (p ≫ ω.1.inv) (sq _ (inv_r ω))
      hom_inv_id := back _ _ (hom_r ω) (inv_r ω) ω.1.hom_inv_id
      inv_hom_id := back _ _ (inv_r ω) (hom_r ω) ω.1.inv_hom_id }
  refine ⟨{ toFun := lift1, map_one' := ?_, map_mul' := ?_ }, fun ω => ⟨h.lift_fst _ _ _, h.lift_snd _ _ _⟩⟩
  · ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = 𝟙 P ≫ φ
      rw [IsPullback.lift_fst, Category.id_comp]
    · change h.lift _ _ _ ≫ p = 𝟙 P ≫ p
      rw [IsPullback.lift_snd, Category.id_comp]
      exact Category.comp_id p
  · intro a b
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = (h.lift φ (p ≫ b.1.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.hom) (sq _ (hom_r a))) ≫ φ
      simp only [IsPullback.lift_fst, Category.assoc]
    · change h.lift _ _ _ ≫ p = (h.lift φ (p ≫ b.1.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.hom) (sq _ (hom_r a))) ≫ p
      simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
      rfl

theorem exists_subgroup_of_finite {G : Type} [Group G] (S : Submonoid G) [Finite S] :
    ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ S := by
  refine ⟨{ S with inv_mem' := fun {x} hx => ?_ }, fun _ => Iff.rfl⟩
  have hx' : IsOfFinOrder x := by
    by_contra hne
    have hinj := injective_pow_iff_not_isOfFinOrder.mpr hne
    exact not_injective_infinite_finite (fun n : ℕ => (⟨x ^ n, S.pow_mem hx n⟩ : S))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  obtain ⟨n, hn⟩ := hx'.mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  rw [← hn]
  exact S.pow_mem hx n

end GlobalTheory.LevQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnimodDiv
section
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTate

theorem exists_local_iso {R : Type} [CommRing R] [IsDedekindDomain R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R M'] (hr : Module.finrank R M = Module.finrank R M') (P : Ideal R) [P.IsPrime] :
    ∃ (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) (s : R), s ∉ P ∧ (∀ a, φ' (φ a) = s • a) ∧ ∀ y, φ (φ' y) = s • y := by
  have hle : P.primeCompl ≤ R⁰ := P.primeCompl_le_nonZeroDivisors
  have : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Flat R M' := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.FinitePresentation R M' := Module.finitePresentation_of_finite R M'
  let S := Localization.AtPrime P
  let N := LocalizedModule P.primeCompl M
  let N' := LocalizedModule P.primeCompl M'
  let j : M →ₗ[R] N := LocalizedModule.mkLinearMap P.primeCompl M
  let j' : M' →ₗ[R] N' := LocalizedModule.mkLinearMap P.primeCompl M'
  have : Module.Free S N := Module.free_of_flat_of_isLocalRing
  have : Module.Free S N' := Module.free_of_flat_of_isLocalRing
  have hr' : Module.finrank S N = Module.finrank S N' := by
    rw [IsLocalization.finrank_eq S P.primeCompl hle, IsLocalization.finrank_eq S P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl j hle, IsLocalizedModule.finrank_eq P.primeCompl j' hle, hr]
  let θ : N ≃ₗ[R] N' := (LinearEquiv.ofFinrankEq N N' hr').restrictScalars R
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j'
    (θ.toLinearMap ∘ₗ j)
  obtain ⟨φ', s', hφ'⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j
    (θ.symm.toLinearMap ∘ₗ j')
  have h1 : ∀ a, j' (φ a) = (s : R) • θ (j a) := fun a => LinearMap.congr_fun hφ a
  have h2 : ∀ a, j (φ' a) = (s' : R) • θ.symm (j' a) := fun a => LinearMap.congr_fun hφ' a
  have hj : Function.Injective j := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j).2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  have hj' : Function.Injective j' := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j').2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  refine ⟨φ, φ', (s * s' : P.primeCompl), (s * s').2, fun a => hj ?_, fun y => hj' ?_⟩
  · rw [h2, h1, map_smul, map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm]; rfl
  · rw [h1, h2, map_smul, map_smul, LinearEquiv.apply_symm_apply, smul_smul]; rfl

theorem mem_of_orth {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m c : ℕ} (hm : m ≠ 0) (hg : m ^ Module.finrank ℤ M = c * c) (C : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C)
    (hc : (nsmulAddMonoidHom (α := M) m).range.relIndex C = c)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (x : M) (hx : ∀ y ∈ C, (m : ℤ) ∣ B x y) : x ∈ C := by
  classical
  have : NeZero m := ⟨hm⟩
  set K := (nsmulAddMonoidHom (α := M) m).range with hK
  have hKi : K.index = c * c := by rw [hK, AddSubgroup.index_range_nsmul, hg]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ hm (by simpa using hg)
  have hCi : C.index = c := by
    have := AddSubgroup.relIndex_mul_index hC
    rw [hc, hKi] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) this
  have : C.FiniteIndex := ⟨hCi ▸ hc0⟩
  let D : AddSubgroup M :=
    { carrier := {x | ∀ y ∈ C, (m : ℤ) ∣ B x y}
      add_mem' := fun {a b} ha hb y hy => by
        rw [map_add, AddMonoidHom.add_apply]; exact (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by
        rw [map_neg, AddMonoidHom.neg_apply]; exact (ha y hy).neg_right }
  have hCD : C ≤ D := fun x hx => hiso x hx
  let f : D → (M ⧸ C →+ ZMod m) := fun x =>
    QuotientAddGroup.lift C ((Int.castAddHom (ZMod m)).comp (B x)) fun y hy =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (x.2 y hy)
  have hf : ∀ (x : D) (y : M), f x (y : M ⧸ C) = (B x y : ZMod m) := fun _ _ => rfl
  let F : D →+ (M ⧸ C →+ ZMod m) := AddMonoidHom.mk' f fun a b => by
    ext y
    simp [hf]
  have hker : F.ker = K.addSubgroupOf D := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h
      have h1 : ∀ y, (m : ℤ) ∣ B x y := fun y =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [← hf]; exact DFunLike.congr_fun h _)
      choose t ht using h1
      have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
      obtain ⟨z, hz⟩ := hB.2 (AddMonoidHom.mk' t fun a b => mul_left_cancel₀ hm' (by
        rw [← ht, map_add, ht, ht, mul_add]))
      refine ⟨z, hB.1 (AddMonoidHom.ext fun y => ?_)⟩
      rw [ht, nsmulAddMonoidHom_apply, map_nsmul, hz]
      simp
    · rintro ⟨z, hz⟩
      ext y
      change f x y = 0
      rw [hf, ← hz, nsmulAddMonoidHom_apply, map_nsmul]
      simp
  have := Fintype.ofFinite (M ⧸ C)
  let T : (M ⧸ C →+ ZMod m) → AddChar (M ⧸ C) ℂ := fun φ => ZMod.stdAddChar.compAddMonoidHom φ
  have hT : Function.Injective T := fun φ ψ h => AddMonoidHom.ext fun x =>
    ZMod.injective_stdAddChar (DFunLike.congr_fun h x)
  have : Finite (M ⧸ C →+ ZMod m) := Finite.of_injective T hT
  have h1 : K.relIndex D ≤ c := by
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
      ((Nat.card_le_card_of_injective T hT).trans_eq ?_)
    rw [← hCi, AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have h2 := AddSubgroup.relIndex_mul_relIndex K C D hC hCD
  have h3 : C.relIndex D ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have h4 : C.relIndex D = 1 := by
    rw [hc] at h2
    have := Nat.pos_of_ne_zero hc0
    have := Nat.pos_of_ne_zero h3
    nlinarith
  exact (AddSubgroup.relIndex_eq_one.1 h4) hx

theorem exists_unimod_div {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {σ : R ≃+* R}
    {B : M →+ M →+ ℤ} (h : IsUnimod σ B) {m : ℕ} (hm : m ≠ 0) (C : Submodule R M) (hC : ∀ a, m • a ∈ C)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (horth : ∀ x, (∀ y ∈ C, (m : ℤ) ∣ B x y) → x ∈ C) :
    ∃ B' : C →+ C →+ ℤ, IsUnimod σ B' ∧ ∀ x y : C, B x y = m * B' x y := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  choose t ht using fun x y : C => hiso x x.2 y y.2
  let B' : C →+ C →+ ℤ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (t x) fun a b => mul_left_cancel₀ hm' (by
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add]))
    fun a b => AddMonoidHom.ext fun y => mul_left_cancel₀ hm' (by
      change m * t (a + b) y = m * (t a y + t b y)
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add, AddMonoidHom.add_apply])
  have hB' : ∀ x y : C, B x y = m * B' x y := ht
  refine ⟨B', ⟨fun x y => mul_left_cancel₀ hm' ?_, fun a x y => mul_left_cancel₀ hm' ?_, ?_, fun f => ?_⟩, hB'⟩
  · rw [mul_neg, ← hB', ← hB', h.skew]
  · rw [← hB', ← hB', Submodule.coe_smul, Submodule.coe_smul, h.adj]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    apply (injective_iff_map_eq_zero _).1 h.bij.1
    ext a
    have := hB' x ⟨m • a, hC a⟩
    rw [hx, map_nsmul] at this
    simpa [hm] using this
  · let u : M →+ C := AddMonoidHom.mk' (fun a => ⟨m • a, hC a⟩) fun a b => Subtype.ext (smul_add _ _ _)
    obtain ⟨x, hx⟩ := h.bij.2 (f.comp u)
    have key : ∀ y : C, B x y = m * f y := fun y => by
      rw [hx, ← nsmul_eq_mul, ← map_nsmul]
      rfl
    refine ⟨⟨x, horth x fun y hy => ⟨_, key ⟨y, hy⟩⟩⟩, AddMonoidHom.ext fun y => mul_left_cancel₀ hm' ?_⟩
    rw [← hB', key]

end GlobalTheory.HeckeTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FourierCoeffEqZeroOfTsumEqZeroFin
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

open Complex Matrix in
open scoped ContDiff BigOperators Real in
private lemma integral_Ioc_cexp_two_pi_I_int_mul (j : ℤ) :
    ∫ t, cexp (2 * π * I * (j : ℂ) * (t : ℂ)) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      if j = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hj
  · subst hj; simp
  · have hc : (2 * π * I * (j : ℂ)) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * (j : ℂ)) = 1 := by
      rw [show 2 * π * I * (j : ℂ) = j * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I j
    simp [h1]

open Complex Matrix in
open scoped ContDiff BigOperators Real in

theorem _root_.GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), Summable (fun ν => ‖c ν‖) →
      (∀ x : Fin n → ℝ, ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = 0) →
      ∀ ν, c ν = 0 := by
  intro n c hc h μ
  set m : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) with hm
  haveI : MeasureTheory.IsProbabilityMeasure m := ⟨by simp [m]⟩
  set P : MeasureTheory.Measure (Fin n → ℝ) := MeasureTheory.Measure.pi fun _ => m
  set G : (Fin n → ℤ) → (Fin n → ℝ) → ℂ := fun ν x =>
    c ν * ∏ k, cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (x k : ℂ)) with hG
  have hnorm : ∀ ν x, ‖G ν x‖ = ‖c ν‖ := by
    intro ν x
    simp only [G, norm_mul, norm_prod, Complex.norm_exp]
    simp [Complex.mul_re]
  have hint : ∀ ν, MeasureTheory.Integrable (G ν) P := by
    intro ν
    refine MeasureTheory.Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      ‖c ν‖ (MeasureTheory.ae_of_all _ fun x => (hnorm ν x).le)
  have hval : ∀ ν, ∫ x, G ν x ∂P = if ν = μ then c ν else 0 := by
    intro ν
    simp only [G]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (μ := fun _ => m) (fun k (t : ℝ) => cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (t : ℂ)))]
    simp only [hm, integral_Ioc_cexp_two_pi_I_int_mul]
    by_cases hνμ : ν = μ
    · subst hνμ; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hνμ
      rw [if_neg hνμ, Finset.prod_eq_zero (Finset.mem_univ k) (by simp [sub_eq_zero, hk]), mul_zero]
  have hsum : ∀ x, ∑' ν, G ν x = 0 := by
    intro x
    have hx := h x
    have : ∀ ν, G ν x = c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) *
        cexp (-(2 * π * I * ∑ k, (μ k : ℂ) * (x k : ℂ))) := by
      intro ν
      simp only [G, mul_assoc]
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    rw [tsum_mul_right, hx, zero_mul]
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hint
    (by simpa [hnorm] using hc)
  simp only [hval, hsum, MeasureTheory.integral_zero] at key
  rwa [tsum_ite_eq] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFlat

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint {O K : Type} [CommRing O] [IsDomain O] [Field K]
    (δ : O →+* K) (pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)) :
    Function.Injective δ := by
  change (Spec.map (CommRingCat.ofHom δ)) pt = genericPoint (Spec (CommRingCat.of O)) at h
  rw [genericPoint_eq_bot_of_affine] at h
  have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime (h := pt.isPrime) _
  have h2 := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap δ pt.asIdeal = ⊥ at h2
  rw [hpt, ← RingHom.ker_eq_comap_bot] at h2
  exact (RingHom.injective_iff_ker_eq_bot δ).mpr h2

theorem exists_charZero_specializes (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0})
    (s : T ⟶ Sp O) [Flat s] (x : T) : ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ) := by
  obtain ⟨ξ, hξ, e⟩ := Flat.generalizingMap s (genericPoint_specializes (s x))
  refine ⟨ξ, hξ, ?_⟩
  obtain ⟨δ, hδ⟩ := Spec.map_surjective (T.fromSpecResidueField ξ ≫ s)
  have hi : Function.Injective δ.hom := by
    refine injective_of_apply_eq_genericPoint (K := T.residueField ξ) δ.hom
      (⊥ : PrimeSpectrum (T.residueField ξ)) ?_
    change Spec.map δ _ = _
    rw [hδ]
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans e)
  exact charZero_of_injective_ringHom hi

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint {O : Type} [CommRing O] [IsDomain O]
    {T : Scheme.{0}} (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) [Flat s]
    {t : T} (ht : t ∈ genericPoints T) : s t = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
  obtain ⟨t', hspec, heq⟩ := Flat.generalizingMap s
    ((genericPoint_spec (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)).specializes (Set.mem_univ (s t)))
  have hsub : closure {t} ⊆ closure {t'} := specializes_iff_closure_subset.mp hspec
  have hcl : closure {t} = closure {t'} :=
    (show closure {t} ∈ irreducibleComponents T from ht).eq_of_le
      isIrreducible_singleton.closure hsub
  have hback : t ⤳ t' := specializes_iff_closure_subset.mpr hcl.ge
  rw [← heq, (hspec.antisymm hback).eq]

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.GenericFlat.generic_charZero_and_flat : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by
  refine ⟨fun O _ _ _ T s hs x => ?_,
    fun R O _ _ _ _ b T s V K _ _ _ _ _ x v hb hs hx hxs => ?_⟩
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x))
    refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
    have hgen : ξ ∈ genericPoints T := by
      change closure {ξ} ∈ irreducibleComponents T
      rw [hξ.def]
      exact irreducibleComponent_mem_irreducibleComponents x
    let δ : O →+* T.residueField ξ := (Spec.preimage (T.fromSpecResidueField ξ ≫ s)).hom
    have hδ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ = T.fromSpecResidueField ξ ≫ s := Spec.map_preimage _
    have hinj : Function.Injective δ := by
      refine _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint δ
        (IsLocalRing.closedPoint (T.residueField ξ)) ?_
      rw [hδ]
      exact (congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans
        (_root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s hgen)
    exact charZero_of_injective_ringHom hinj
  · let φ : O →+* V := (Spec.preimage v).hom
    have hv : v = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ := (Spec.map_preimage v).symm
    have hcomp : x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) := by
      rw [hxs, hv]; exact (Spec.map_comp _ _).symm
    let pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K := IsLocalRing.closedPoint K
    have hpt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
      rw [← hcomp, Scheme.Hom.comp_apply]
      exact _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s (hx ⟨pt, rfl⟩)
    have hφ : Function.Injective φ := by
      have h := _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ pt hpt
      rw [RingHom.coe_comp] at h
      exact h.of_comp
    have hψ : Function.Injective (φ.comp b) := hφ.comp hb
    have hmap : v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b = Spec.map (CommRingCat.ofHom (φ.comp b)) := by
      rw [hv]; exact (Spec.map_comp _ _).symm
    rw [hmap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (φ.comp b).toAlgebra
    change Module.Flat R V
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff m).mp hm
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at ha
    have h0 : (φ.comp b) a ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero a (hψ (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp ha).resolve_left h0

end GlobalTheory.GenericFlat
end

