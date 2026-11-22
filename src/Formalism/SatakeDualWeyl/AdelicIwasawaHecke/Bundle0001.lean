import Formalism.SatakeDualWeyl.Statement

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
section
namespace Formalism.UG.P

open Matrix MvPolynomial

theorem standard_action_mul_holds : Formalism.UG.StdActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.stdAct
    rw [Units.val_mul, Matrix.mulVecLin_mul]
  · unfold Formalism.UG.stdAct
    rw [Units.val_one, Matrix.mulVecLin_one]

theorem tensor_action_mul_holds : Formalism.UG.TensActMul := by
  intro O _ n _ _ k g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.tensAct
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext i
    exact (standard_action_mul_holds O n g h).1
  · unfold Formalism.UG.tensAct
    have : (fun _ : Fin k => Formalism.UG.stdAct O n 1) = fun _ => LinearMap.id :=
      funext fun _ => (standard_action_mul_holds O n 1 1).2
    rw [this, PiTensorProduct.map_id]

theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]

theorem polynomial_action_mul_holds : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AssocFin
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

private lemma smul_quotient_mk (g x : G) : (g • (x : G ⧸ K)) = ((g * x : G) : G ⧸ K) := rfl

private lemma subgroup_smul_quotient_mk (k : K) (x : G) : (k • (x : G ⧸ K)) = (((k : G) * x : G) : G ⧸ K) := rfl

theorem stabilizer_coset_eq (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map, subgroup_smul_quotient_mk,
    QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨s⁻¹ * k * s, ?_, ?_⟩
    · have := K.inv_mem hk
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨t, ht, hts⟩
    rw [← hts]
    simpa [MulAut.conj_apply, mul_assoc] using K.inv_mem ht

theorem orbit_coset_finite (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by
  have h1 : ((K.map (MulAut.conj s).toMonoidHom).subgroupOf K).index ≠ 0 := hK s
  rw [← stabilizer_coset_eq] at h1
  haveI : Finite (K ⧸ MulAction.stabilizer K ((s : G ⧸ K))) := Nat.finite_of_card_ne_zero h1
  exact Set.finite_coe_iff.mp ((MulAction.orbitEquivQuotientStabilizer K _).finite_iff.mpr this)

theorem finite_supp_translate (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s).image (fun y : G ⧸ K => h⁻¹ • y)).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a • ((s : G ⧸ K)), ⟨a, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk]
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  have hx' : x.out = h⁻¹ * ((a : G) * s * b) := by rw [← hab]; group
  rw [hx']
  convert b.2 using 1
  group

theorem finite_supp_inv (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (g : G) :
    {y : G ⧸ K | f (y.out⁻¹ * g) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s⁻¹).image (fun y : G ⧸ K => g • y)).subset ?_
  intro y hy
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hy
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨b⁻¹ • (((s⁻¹ : G)) : G ⧸ K), ⟨b⁻¹, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk, Subgroup.coe_inv]
  rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
  have hy' : y.out = g * ((a : G) * s * b)⁻¹ := by rw [← hab]; group
  rw [hy']
  convert K.inv_mem a.2 using 1
  group

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (DoubleCoset.eq Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

theorem mk_of_eq (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    DoubleCoset.mk Γ K g = c := by
  conv_rhs => rw [← hs c]
  rw [DoubleCoset.eq]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, ?_⟩
  rw [e]
  group

theorem rho_eq_of_eq {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ W) (x : G) (w : W)
    (hw : ∀ γ ∈ stabAt Γ K x, ρ γ w = w) (γ γ' : Γ) (κ κ' : K)
    (e : (γ : G) * x * κ = (γ' : G) * x * κ') : ρ γ w = ρ γ' w := by
  have e' : (γ : G) = (γ' : G) * x * (κ' : G) * (κ : G)⁻¹ * x⁻¹ := by
    rw [← e]
    group
  have hmem : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x ∈ K := by
    have h1 : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x = (κ' : G) * (κ : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e']
      group
    rw [h1]
    exact K.mul_mem κ'.2 (K.inv_mem κ.2)
  have h := hw (γ'⁻¹ * γ) hmem
  calc ρ γ w = ρ (γ' * (γ'⁻¹ * γ)) w := by rw [mul_inv_cancel_left]
    _ = ρ γ' (ρ (γ'⁻¹ * γ) w) := by rw [map_mul]; rfl
    _ = ρ γ' w := by rw [h]

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

def extend (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W) (g : G) : W :=
  ρ (Classical.choose (exists_rep Γ K s hs g)).1 (w (DoubleCoset.mk Γ K g))

theorem extend_eq (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W)
    (hw : ∀ c, ∀ γ ∈ stabAt Γ K (s c), ρ γ (w c) = w c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    extend Γ K s hs ρ w g = ρ γ (w c) := by
  have hc : DoubleCoset.mk Γ K g = c := mk_of_eq Γ K s hs c g γ κ e
  have hp := Classical.choose_spec (exists_rep Γ K s hs g)
  unfold extend
  generalize Classical.choose (exists_rep Γ K s hs g) = p at hp ⊢
  rw [hc] at hp ⊢
  exact rho_eq_of_eq Γ K ρ (s c) (w c) (hw c) p.1 γ p.2 κ (hp.symm.trans e)

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

abbrev conjInter (K : Subgroup G) (s : G) : Subgroup K :=
  (K.map (MulAut.conj s).toMonoidHom).subgroupOf K

theorem finite_quot_conjInter {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by
  haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩
  exact Subgroup.finite_quotient_of_finiteIndex

theorem mul_eq_out_mul (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (conjInter K s) k
  have hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s := (h⁻¹).2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hmem
  obtain ⟨m, hmK, hm⟩ := hmem
  refine ⟨⟨m, hmK⟩, ?_⟩
  rw [hh]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm
  have hm' : s * m = ((h : K) : G)⁻¹ * s := by
    rw [← hm]; group
  simp only [Subgroup.coe_mul]
  rw [mul_assoc _ s, hm']
  group

theorem finite_cosets_in_doset {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * s * b}.Finite := by
  haveI := finite_quot_conjInter hK s
  refine (Set.finite_range
    (fun y : K ⧸ conjInter K s => ((((y.out : K) : G) * s : G) : G ⧸ K))).subset ?_
  rintro x ⟨a, b, hx⟩
  obtain ⟨k', hk'⟩ := mul_eq_out_mul K s a
  refine ⟨QuotientGroup.mk a, ?_⟩
  dsimp only
  have hxx : (QuotientGroup.mk x.out : G ⧸ K) = x := Quotient.out_eq x
  rw [← hxx, hx, hk', QuotientGroup.eq]
  have e : ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s)⁻¹ *
      ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s * k' * b) = k' * b := by
    group
  rw [e]
  exact K.mul_mem k'.2 b.2

theorem finite_support_cosets {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, h⟩ := hS _ hx
  exact Set.mem_biUnion hs ⟨a, b, h⟩

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem out_smul (K : Subgroup G) (c : G) (x : G ⧸ K) :
    ∃ κ : K, (c • x).out = c * x.out * (κ : G) := by
  have h : ((c * x.out : G) : G ⧸ K) = ((c • x).out : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk]
    rfl
  refine ⟨⟨_, QuotientGroup.eq.1 h⟩, ?_⟩
  simp only [mul_inv_cancel_left]

theorem finsum_out_mul {M : Type} [AddCommMonoid M] (K : Subgroup G) (a : G) (F : G → M)
    (hF : ∀ (g : G) (c : K), F (g * c) = F g) :
    ∑ᶠ z : G ⧸ K, F (a * z.out) = ∑ᶠ y : G ⧸ K, F y.out := by
  have h : ∀ z : G ⧸ K, F (a * z.out) = F (a • z).out := by
    intro z
    obtain ⟨κ, hκ⟩ := out_smul K a z
    rw [hκ, hF]
  rw [finsum_congr h]
  exact finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun y => F y.out)

theorem finite_supp {k : Type} [CommRing k] (K : Subgroup G) (hK : IsCommensurated K)
    (f : G → k) (hf : f ∈ Hecke k K) : {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  obtain ⟨-, S, hS⟩ := hf'
  unfold IsCommensurated at hK
  have hfin : ∀ s : G, (Set.range fun k : K => ((↑k * s : G) : G ⧸ K)).Finite := by
    intro s
    let H : Subgroup K := (Subgroup.map (MulAut.conj s).toMonoidHom K).subgroupOf K
    haveI : H.FiniteIndex := ⟨hK s⟩
    haveI : Finite (K ⧸ H) := inferInstance
    let φ : K ⧸ H → G ⧸ K := Quotient.lift (fun k : K => ((↑k * s : G) : G ⧸ K)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
      have h2 : ((a⁻¹ * b : K) : G) ∈ Subgroup.map (MulAut.conj s).toMonoidHom K :=
        Subgroup.mem_subgroupOf.1 hab'
      obtain ⟨c, hc, hcab⟩ := Subgroup.mem_map.1 h2
      have e : (a : G)⁻¹ * b = s * c * s⁻¹ := by
        rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← hcab]
        rfl
      apply QuotientGroup.eq.2
      have : ((a : G) * s)⁻¹ * ((b : G) * s) = c := by
        calc ((a : G) * s)⁻¹ * ((b : G) * s) = s⁻¹ * ((a : G)⁻¹ * b) * s := by group
          _ = c := by rw [e]; group
      rw [this]
      exact hc)
    refine (Set.finite_range φ).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : K ⧸ H), rfl⟩
  refine (S.finite_toSet.biUnion fun s _ => hfin s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' x]
  apply QuotientGroup.eq.2
  rw [hab]
  have : ((a : G) * s)⁻¹ * ((a : G) * s * b) = b := by group
  rw [this]
  exact b.2

theorem amf_right {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    {Γ K : Subgroup G} {ρ : Representation k Γ W} {φ : G → W} (hφ : φ ∈ AMF k Γ K ρ)
    (g : G) (c : K) : φ (g * c) = φ g := by
  have h : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  simpa using h 1 g c

theorem hecke_act_mem : Formalism.UG.HeckeActMem := by
  intro G _ Γ K k _ W _ _ ρ hK f hf φ hφ
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  have hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g := hf'.1
  have hφ' : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  have hfin := finite_supp K hK f hf
  show ∀ (γ : Γ) (g : G) (κ : K), hAct K f φ (↑γ * g * ↑κ) = ρ γ (hAct K f φ g)
  intro γ g κ
  simp only [hAct]
  have step1 : ∀ x : G ⧸ K, f x.out • φ (↑γ * g * ↑κ * x.out) =
      ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) := by
    intro x
    obtain ⟨κ', hκ'⟩ := out_smul K (κ : G) x
    have h1 : x.out = (κ : G)⁻¹ * ((κ : G) • x).out * (κ' : G)⁻¹ := by rw [hκ']; group
    have e1 : f x.out = f ((κ : G) • x).out := by
      rw [h1]
      have := hbi κ⁻¹ κ'⁻¹ ((κ : G) • x).out
      simpa using this
    have e2 : φ (↑γ * g * ↑κ * x.out) = ρ γ (φ (g * ((κ : G) • x).out)) := by
      have : (↑γ : G) * g * ↑κ * x.out = ↑γ * (g * ((κ : G) • x).out) * ↑(κ'⁻¹) := by
        rw [h1, Subgroup.coe_inv]
        group
      rw [this, hφ']
    rw [e1, e2, map_smul]
  rw [finsum_congr step1]
  have hre : ∑ᶠ x : G ⧸ K, ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) =
      ∑ᶠ y : G ⧸ K, ρ γ (f y.out • φ (g * y.out)) :=
    finsum_comp_equiv (MulAction.toPerm (κ : G) : Equiv.Perm (G ⧸ K))
      (f := fun y => ρ γ (f y.out • φ (g * y.out)))
  rw [hre]
  have hsupp : (Function.support fun y : G ⧸ K => f y.out • φ (g * y.out)).Finite :=
    hfin.subset fun y hy => by
      intro h0
      exact hy (by simp [h0])
  exact (map_finsum (ρ γ) hsupp).symm

private theorem finite_support_left_translate_of_biinvariant {k : Type} [CommRing k] (K : Subgroup G) (f : G → k)
    (hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g) (hfin : {x : G ⧸ K | f x.out ≠ 0}.Finite)
    (a : G) : {x : G ⧸ K | f (a * x.out) ≠ 0}.Finite := by
  refine (hfin.preimage (f := fun x : G ⧸ K => a • x)
    fun _ _ _ _ h => MulAction.injective a h).subset ?_
  intro x hx
  show f (a • x).out ≠ 0
  obtain ⟨κ, hκ⟩ := out_smul K a x
  rw [hκ]
  have e : f (a * x.out * ↑κ) = f (a * x.out) := by simpa using hbi 1 κ (a * x.out)
  rw [e]
  exact hx

theorem hecke_act_mul : Formalism.UG.HeckeActMul := by
  intro G _ Γ K k _ W _ _ ρ hK f₁ hf₁ f₂ hf₂ φ hφ
  have hbi₂ : ∀ (a b : K) (g : G), f₂ (↑a * g * ↑b) = f₂ g :=
    (show IsBiInv K f₂ ∧ FinDosetSupp K f₂ from hf₂).1
  have hfin₁ := finite_supp K hK f₁ hf₁
  have hfin₂ := finite_supp K hK f₂ hf₂
  funext g
  simp only [hAct, conv]
  have hA : ∀ y : G ⧸ K, ∑ᶠ z : G ⧸ K, f₂ z.out • φ (g * y.out * z.out) =
      ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    intro y
    have := finsum_out_mul K y.out (fun h => f₂ (y.out⁻¹ * h) • φ (g * h)) (by
      intro h c
      show f₂ (y.out⁻¹ * (h * ↑c)) • φ (g * (h * ↑c)) = f₂ (y.out⁻¹ * h) • φ (g * h)
      rw [(by simp [mul_assoc] : y.out⁻¹ * (h * ↑c) = ↑(1 : K) * (y.out⁻¹ * h) * ↑c), hbi₂,
        (by rw [mul_assoc] : g * (h * ↑c) = g * h * ↑c), amf_right hφ])
    simpa [mul_assoc] using this
  simp_rw [hA]
  set A := hfin₁.toFinset with hAdef
  have hB : ∀ y : G ⧸ K, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}.Finite :=
    fun y => finite_support_left_translate_of_biinvariant K f₂ hbi₂ hfin₂ y.out⁻¹
  have hX : (⋃ y ∈ A, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}).Finite :=
    A.finite_toSet.biUnion fun y _ => hB y
  set X := hX.toFinset with hXdef
  have hAsub : ∀ y : G ⧸ K, f₁ y.out ≠ 0 → y ∈ A := fun y hy => hfin₁.mem_toFinset.2 hy
  have hXsub : ∀ y x : G ⧸ K, f₁ y.out ≠ 0 → f₂ (y.out⁻¹ * x.out) ≠ 0 → x ∈ X := by
    intro y x h1 h2
    rw [hX.mem_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 (hAsub y h1)) h2
  have hL : ∀ x : G ⧸ K, ∑ᶠ y : G ⧸ K, f₁ y.out * f₂ (y.out⁻¹ * x.out) =
      ∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out) := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro y hy
    exact hAsub y (left_ne_zero_of_mul hy)
  simp_rw [hL]
  have eL : ∑ᶠ x : G ⧸ K, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) =
      ∑ x ∈ X, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) := by
    apply finsum_eq_sum_of_support_subset
    intro x hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_smul hx)
    exact hXsub y x (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)
  have eR : ∑ᶠ y : G ⧸ K, f₁ y.out • ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) =
      ∑ y ∈ A, f₁ y.out • ∑ x ∈ X, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    rw [finsum_eq_sum_of_support_subset (s := A) _ (fun y hy => hAsub y (left_ne_zero_of_smul hy))]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [finsum_eq_sum_of_support_subset (s := X) _
      (fun x hx => hXsub y x (hfin₁.mem_toFinset.1 hy) (left_ne_zero_of_smul hx))]
  rw [eL, eR]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_setOf_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

theorem card_stabAt_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ.1 * γ, (mem_stabAt_mul_iff Γ K g γ κ δ.1).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ.1 * γ⁻¹, (mem_stabAt_mul_iff Γ K g γ κ _).2 (by
        convert δ.2 using 2; group)⟩
      left_inv := fun δ => Subtype.ext (by group)
      right_inv := fun δ => Subtype.ext (by group) }

theorem inner_product_independent : Formalism.UG.IpIndep := by
  intro G _ Γ K k _ _ W _ _ ρ _ B hB s s' hs hs' _ f hf f' hf'
  have hf2 : ∀ (γ : Γ) (g : G) (κ : K), f ((γ : G) * g * κ) = ρ γ (f g) := hf
  have hf2' : ∀ (γ : Γ) (g : G) (κ : K), f' ((γ : G) * g * κ) = ρ γ (f' g) := hf'
  unfold ipAMF
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨γ, hγ, κ, hκ, he⟩ := (DoubleCoset.eq _ _ (s c) (s' c)).1 ((hs c).trans (hs' c).symm)
  have h1 : s' c = ((⟨γ, hγ⟩ : Γ) : G) * s c * ((⟨κ, hκ⟩ : K) : G) := he
  rw [h1, card_stabAt_mul, hf2, hf2', hB]

end Formalism.UG.P
end
end

