import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig
section
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig_holds :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig := by
  intro Γ H Z V _ _ _ _ _ ι K ξ _ ζ hc M hM hne hst
  haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hM
  haveI : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hne
  let R : Z → Module.End ℂ M := fun z =>
    { toFun := fun Φ => ⟨fun g => (Φ : H → V) (g * ζ z), hst Φ Φ.2 z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcomm : ∀ i j : Z, R i * R j = R j * R i := by
    intro i j
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun g => ?_)
    change (Φ : H → V) (g * ζ i * ζ j) = (Φ : H → V) (g * ζ j * ζ i)
    rw [mul_assoc, mul_assoc, hc i (ζ j)]
  obtain ⟨v, -, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig R hcomm _ (⊤ : Submodule ℂ M) rfl top_ne_bot
    (fun _ _ _ => Submodule.mem_top)
  choose a ha using hv
  have hΦ : ∀ z g, (v : H → V) (g * ζ z) = a z • (v : H → V) g := fun z g =>
    congrFun (congrArg Subtype.val (ha z)) g
  have hv0' : (v : H → V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hv0'
  have hg₀' : (v : H → V) g₀ ≠ 0 := hg₀
  have cancel : ∀ b c : ℂ, b • (v : H → V) g₀ = c • (v : H → V) g₀ → b = c :=
    fun b c h => smul_left_injective ℂ hg₀' h
  have a1 : a 1 = 1 := by
    apply cancel
    rw [← hΦ, map_one, mul_one, one_smul]
  have amul : ∀ x y, a (x * y) = a x * a y := by
    intro x y
    apply cancel
    rw [← hΦ, map_mul, ← mul_assoc, hΦ, hΦ, smul_smul, mul_comm]
  let ψ : Z →* ℂˣ := ({ toFun := a, map_one' := a1, map_mul' := amul } : Z →* ℂ).toHomUnits
  have hψ : ∀ z, (ψ z : ℂ) = a z := fun z => by
    simp only [ψ, MonoidHom.coe_toHomUnits]
    rfl
  refine ⟨(v : H → V), v.2, hv0', ψ, ?_, ?_, ?_⟩
  · intro z g
    rw [hψ, hΦ]
  · intro z hz
    apply Units.ext
    rw [hψ, Units.val_one]
    apply cancel
    rw [← hΦ, one_smul]
    exact (hM v.2).2 _ hz g₀
  · intro z γ b hz hb
    rw [hψ]
    apply cancel
    rw [← hΦ, ← hb, ← hc z g₀, hz]
    exact (hM v.2).1 γ g₀
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCertProj
section
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem wop_sub_mem {F B J : Type*} [Field F] [CommRing B] [Algebra F B] (I : Ideal B)
    (T : J → B) (θ : J → F) (h : ∀ j, T j - algebraMap F B (θ j) ∈ I) (s : List J →₀ F) :
    wop T s - algebraMap F B (wop θ s) ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hT : (fun j => Ideal.Quotient.mkₐ F I (T j)) =
      fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j) := by
    funext j
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h j)
  calc Ideal.Quotient.mk I (wop T s) = Ideal.Quotient.mkₐ F I (wop T s) := rfl
    _ = wop (fun j => Ideal.Quotient.mkₐ F I (T j)) s := map_wop _ _ _
    _ = wop (fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j)) s := by rw [hT]
    _ = ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (wop θ s) := (map_wop _ _ _).symm
    _ = Ideal.Quotient.mk I (algebraMap F B (wop θ s)) := rfl

private theorem fix_of_cert {F B W J : Type*} [Field F] [CommRing B] [Algebra F B] [AddCommGroup W]
    [Module F W] (g : B →ₐ[F] End F W) (T' : J → B) (θ : J → F) (t : List J →₀ F)
    (h1 : wop θ t = 1) (h2 : IsIdempotentElem (wop (fun j => g (T' j)) t)) (x : W)
    (hx : ∀ j, ∃ k : ℕ, ((g (T' j) - algebraMap F (End F W) (θ j)) ^ k) x = 0) :
    wop (fun j => g (T' j)) t x = x := by
  let A : Ideal B :=
    { carrier := {b | g b x = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c b hb
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [map_mul, Module.End.mul_apply, hb, map_zero] }
  have hmem : ∀ b : B, (∃ k : ℕ, ((g b) ^ k) x = 0) → b ∈ A.radical := by
    rintro b ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show g (b ^ k) x = 0
    rw [map_pow]
    exact hk
  have hmem' : ∀ b ∈ A.radical, ∃ k : ℕ, ((g b) ^ k) x = 0 := by
    rintro b ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact hk
  have hT : ∀ j, T' j - algebraMap F B (θ j) ∈ A.radical := by
    intro j
    apply hmem
    obtain ⟨k, hk⟩ := hx j
    refine ⟨k, ?_⟩
    rw [map_sub, AlgHom.commutes]
    exact hk
  have hw := wop_sub_mem A.radical T' θ hT t
  rw [h1, map_one] at hw
  obtain ⟨k, hk⟩ := hmem' _ (A.radical.neg_mem hw)
  rw [neg_sub, map_sub, map_one, map_wop] at hk
  have hid := h2.one_sub
  cases k with
  | zero =>
    simp at hk
    simp [hk]
  | succ m =>
    rw [hid.pow_succ_eq m] at hk
    have hk2 : x - wop (fun j => g (T' j)) t x = 0 := by simpa using hk
    exact (sub_eq_zero.mp hk2).symm

end UpperTheory.Gal.CertificateRingHomMap

theorem UpperTheory.Gal.CertificateRingHomMap.pCertProj_holds :
    UpperTheory.Gal.CertificateRingHomMap.CertProj.{u} := by
  rintro F _ W _ _ J T hc θ t ⟨h1, h2, h3⟩
  constructor
  · intro x
    rw [Submodule.mem_iInf]
    intro j
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨N, hN⟩ := h3 j
    refine ⟨N, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, ← Module.End.mul_apply, hN, LinearMap.zero_apply]
  · intro x hx
    have hs : ∀ a ∈ Set.range T, ∀ b ∈ Set.range T, a * b = b * a := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hc i j
    letI : CommRing (Algebra.adjoin F (Set.range T)) := Algebra.adjoinCommRingOfComm F hs
    let T' : J → Algebra.adjoin F (Set.range T) := fun j => ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    refine fix_of_cert (Algebra.adjoin F (Set.range T)).val T' θ t h1 h2 x ?_
    intro j
    have hj := (Submodule.mem_iInf _).mp hx j
    rw [Module.End.mem_maxGenEigenspace] at hj
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by rw [Algebra.algebraMap_eq_smul_one]; exact hk⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig
section
open Module

universe u v

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp [rop, Finsupp.sum, Finset.sum_add_distrib, smul_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Finsupp.sum, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => smul_comm _ _ _

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

private theorem ext_eig_at {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ Φ : H → V}
    (hΦ : Φ ∈ forms ι K ξ) (hres : ∀ u, c u = 1 → Φ u = φ u)
    (hsupp : ∀ g, Φ g ≠ 0 → ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k)
    {r : H →₀ ℂ} {θ : ℂ} (hr : ∀ u ∈ r.support, c u = 1) (hform : rop r Φ ∈ forms ι K ξ)
    (hφ : ∀ u, c u = 1 → rop r φ u = θ • φ u) : rop r Φ = θ • Φ := by
  classical
  have key : ∀ u, c u = 1 → rop r Φ u = θ • Φ u := by
    intro u hu
    rw [hres u hu, ← hφ u hu]
    refine Finsupp.sum_congr fun u' hu' => ?_
    rw [hres _ (by rw [map_mul, hu, hr u' hu', one_mul])]
  funext g
  by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
  · obtain ⟨γ, u, k, hu, hk, rfl⟩ := hg
    have h1 := hform.2 k hk (ι γ * u)
    have h2 := hΦ.2 k hk (ι γ * u)
    have h3 := hform.1 γ u
    have h4 := hΦ.1 γ u
    rw [h1, h3, Pi.smul_apply, h2, h4, key u hu, map_smul]
  · have h0 : ∀ g', (¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g' = ι γ * u * k) → Φ g' = 0 := by
      intro g' hg'
      by_contra hne
      exact hg' (hsupp g' hne)
    have h1 : ∀ u' ∈ r.support, Φ (g * u') = 0 := by
      intro u' hu'
      apply h0
      rintro ⟨γ, u, k, hu, hk, he⟩
      refine hg ⟨γ, u * (k * u'⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
      · simp [map_mul, map_inv, hu, hr u' hu']
      · have : g = ι γ * u * k * u'⁻¹ := by rw [← he]; group
        rw [this]; group
    rw [Pi.smul_apply, h0 g hg, smul_zero]
    unfold rop
    exact Finset.sum_eq_zero fun u' hu' => by
      show r u' • Φ (g * u') = 0
      rw [h1 u' hu', smul_zero]

end

theorem pExtEig_holds : ExtZero → CentralEig → ExtEig := by
  intro hZ hC Γ H A Z V _ _ _ _ _ _ ι K ξ _ c ζ hζ φ hφ hne J r θ hr hforms heig
  obtain ⟨Φ₀, hΦ₀, hres, hsupp⟩ := hZ Γ H A V ι K ξ c φ hφ
  have hM0 : Φ₀ ∈ eigForms ι K ξ r θ := ⟨hΦ₀, fun j =>
    ext_eig_at hΦ₀ hres hsupp (hr j) (hforms j Φ₀ hΦ₀) (heig j)⟩
  have hMle : eigForms ι K ξ r θ ≤ forms ι K ξ := fun Φ h => h.1
  have hMne : eigForms ι K ξ r θ ≠ ⊥ := by
    intro hb
    obtain ⟨u, hu, hu'⟩ := hne
    have h0 : Φ₀ = 0 := by
      have : Φ₀ ∈ (⊥ : Submodule ℂ (H → V)) := hb ▸ hM0
      simpa using this
    apply hu'
    rw [← hres u hu, h0]
    rfl
  have hstable : ∀ Φ ∈ eigForms ι K ξ r θ, ∀ z, (fun g => Φ (g * ζ z)) ∈ eigForms ι K ξ r θ := by
    rintro Φ ⟨hΦ, hΦ'⟩ z
    refine ⟨⟨fun γ g => ?_, fun k hk g => ?_⟩, fun j => ?_⟩
    · show Φ (ι γ * g * ζ z) = ξ γ (Φ (g * ζ z))
      rw [mul_assoc, hΦ.1]
    · show Φ (g * k * ζ z) = Φ (g * ζ z)
      rw [mul_assoc, ← hζ z k, ← mul_assoc, hΦ.2 k hk]
    · funext g
      have h := congrFun (hΦ' j) (g * ζ z)
      rw [Pi.smul_apply] at h ⊢
      rw [← h]
      unfold rop
      refine Finsupp.sum_congr fun u _ => ?_
      show (r j) u • Φ (g * u * ζ z) = (r j) u • Φ (g * ζ z * u)
      rw [mul_assoc g u, ← hζ z u, ← mul_assoc]
  obtain ⟨Φ, hΦ, hΦ0, ψ, hψ⟩ := hC Γ H Z V ι K ξ ζ hζ (eigForms ι K ξ r θ) hMle hMne hstable
  exact ⟨Φ, hΦ.1, hΦ0, hΦ.2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtHecke
section
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators

open GlobalTheory.LKDef.HeckeTraceForms

variable {H A : Type} [Group H] [Group A]

private theorem finsum_comp_inj {α β M : Type*} [AddCommMonoid M] {m : α → β}
    (hm : Function.Injective m) (f : β → M) (hs : Function.support f ⊆ Set.range m) :
    ∑ᶠ b, f b = ∑ᶠ a, f (m a) := by
  rw [← finsum_mem_range hm, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

private theorem mk_injective (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) :
    Function.Injective (fun q : c.ker ⧸ K.subgroupOf c.ker =>
      (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K)) := by
  intro a b hab
  have h1 : ((a.out : H) * w)⁻¹ * ((b.out : H) * w) ∈ K := QuotientGroup.eq.1 hab
  have e : ((a.out : H) * w)⁻¹ * ((b.out : H) * w) = (a.out : H)⁻¹ * (b.out : H) := by
    rw [← hw (a.out : H), ← hw (b.out : H)]; group
  rw [e] at h1
  have h2 : (a.out)⁻¹ * b.out ∈ K.subgroupOf c.ker := Subgroup.mem_subgroupOf.2 (by simpa using h1)
  calc a = QuotientGroup.mk a.out := (QuotientGroup.out_eq' a).symm
    _ = QuotientGroup.mk b.out := QuotientGroup.eq.2 h2
    _ = b := QuotientGroup.out_eq' b

private theorem out_inv {X : Type*} (K : Subgroup H) {G : H → X} (hG : ∀ k ∈ K, ∀ g, G (g * k) = G g)
    (x : H) : G ((QuotientGroup.mk x : H ⧸ K).out) = G x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]; exact hG k k.2 x

private theorem mem_range_mk (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) {F : H → ℂ}
    (hsup : ∀ g, F g ≠ 0 → ∃ u k, c u = 1 ∧ k ∈ K ∧ g = u * w * k) (h : H ⧸ K) (hh : F h.out ≠ 0) :
    h ∈ Set.range (fun q : c.ker ⧸ K.subgroupOf c.ker =>
      (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K)) := by
  obtain ⟨u, k, hu, hk, e⟩ := hsup _ hh
  have huk : u ∈ c.ker := MonoidHom.mem_ker.2 hu
  obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf c.ker) (⟨u, huk⟩ : c.ker)
  refine ⟨QuotientGroup.mk ⟨u, huk⟩, ?_⟩
  have e1 : (((QuotientGroup.mk ⟨u, huk⟩ : c.ker ⧸ K.subgroupOf c.ker).out : c.ker) : H)
      = u * ((k' : c.ker) : H) := by
    rw [hk']; rfl
  have e2 : h = (QuotientGroup.mk (u * w) : H ⧸ K) :=
    calc h = QuotientGroup.mk h.out := (QuotientGroup.out_eq' h).symm
      _ = QuotientGroup.mk (u * w * k) := by rw [← e]
      _ = QuotientGroup.mk (u * w) := QuotientGroup.mk_mul_of_mem _ hk
  have e3 : u * ((k' : c.ker) : H) * w = u * w * ((k' : c.ker) : H) := by
    rw [mul_assoc, ← hw, mul_assoc]
  show (QuotientGroup.mk (((QuotientGroup.mk ⟨u, huk⟩ : c.ker ⧸ K.subgroupOf c.ker).out : H) * w) : H ⧸ K) = h
  rw [e1, e3, e2]
  exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.1 k'.2)

private theorem hecke_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c : H →* A) (K : Subgroup H) {w : H}
    (hw : ∀ g, w * g = g * w) {F : H → ℂ} (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g)
    (hsup : ∀ g, F g ≠ 0 → ∃ u k, c u = 1 ∧ k ∈ K ∧ g = u * w * k)
    (Φ : H → V) (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : H) :
    ∑ᶠ h : H ⧸ K, F h.out • Φ (g * h.out) =
      ∑ᶠ q : c.ker ⧸ K.subgroupOf c.ker, F ((q.out : H) * w) • Φ (g * ((q.out : H) * w)) := by
  rw [finsum_comp_inj (mk_injective c K hw) (fun h : H ⧸ K => F h.out • Φ (g * h.out))]
  · refine finsum_congr fun q => ?_
    have hG : ∀ k ∈ K, ∀ x, Φ (g * (x * k)) = Φ (g * x) := fun k hk x => by
      rw [← mul_assoc, hΦ k hk]
    show F (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out •
        Φ (g * (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out) = _
    rw [out_inv K hFK, out_inv K (G := fun x => Φ (g * x)) hG]
  · intro h hh
    refine mem_range_mk c K hw hsup h fun h0 => hh ?_
    simp [h0]

private theorem finite_supp (c : H →* A) (K : Subgroup H) {w : H} (hw : ∀ g, w * g = g * w) {F : H → ℂ}
    (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g) (hfin : Set.Finite {h : H ⧸ K | F h.out ≠ 0}) :
    Set.Finite {q : c.ker ⧸ K.subgroupOf c.ker | F ((q.out : H) * w) ≠ 0} := by
  refine (hfin.preimage (mk_injective c K hw).injOn).subset fun q hq => ?_
  show F (QuotientGroup.mk ((q.out : H) * w) : H ⧸ K).out ≠ 0
  rw [out_inv K hFK]
  exact hq

private theorem exists_r {V : Type} [AddCommGroup V] [Module ℂ V] (c : H →* A) (K : Subgroup H) {w : H}
    (hw : ∀ g, w * g = g * w) {F : H → ℂ} (hFK : ∀ k ∈ K, ∀ g, F (g * k) = F g)
    (hfin : Set.Finite {h : H ⧸ K | F h.out ≠ 0}) :
    ∃ r : H →₀ ℂ, (∀ u ∈ r.support, c u = 1) ∧ ∀ (Ψ : H → V) (g : H),
      rop r Ψ g = ∑ᶠ q : c.ker ⧸ K.subgroupOf c.ker, F ((q.out : H) * w) • Ψ (g * (q.out : H)) := by
  classical
  have hs := finite_supp c K hw hFK hfin
  refine ⟨∑ q ∈ hs.toFinset, Finsupp.single (q.out : H) (F ((q.out : H) * w)), fun u hu => ?_,
    fun Ψ g => ?_⟩
  · obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
    have : u = (q.out : H) := by simpa using Finsupp.support_single_subset hq
    rw [this]
    exact MonoidHom.mem_ker.1 q.out.2
  · unfold rop
    rw [← Finsupp.sum_finset_sum_index (h := fun u (a : ℂ) => a • Ψ (g * u)) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
    rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · refine Finset.sum_congr rfl fun q _ => ?_
      exact Finsupp.sum_single_index (zero_smul _ _)
    · intro q hq
      have : F ((q.out : H) * w) ≠ 0 := fun h0 => hq (by simp [h0])
      simpa using this

end UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators

open UpperTheory.Gal.CertificateRingHomMap.ExtensionHeckeOperators GlobalTheory.LKDef.HeckeTraceForms in
theorem UpperTheory.Gal.CertificateRingHomMap.pExtHecke_holds :
    UpperTheory.Gal.CertificateRingHomMap.ExtEig → UpperTheory.Gal.CertificateRingHomMap.ExtHecke := by
  intro hE Γ H A Z V _ _ _ _ _ _ ι K ξ _ c ζ hζ φ hφ hne J F z T θ hT hFK hfin hsup hθ
  have hw : ∀ j, ∀ g, ζ (z j) * g = g * ζ (z j) := fun j => hζ (z j)
  have mem : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun _ => Iff.rfl
  have hFK' : ∀ j, ∀ k ∈ K, ∀ g, F j (g * k) = F j g := hFK
  choose r hr1 hr2 using fun j => exists_r (V := V) c K (hw j) (hFK' j) (hfin j)
  have hT' : ∀ j (Ψ : forms ι K ξ) g, (T j Ψ : H → V) g = rop (r j) (Ψ : H → V) (g * ζ (z j)) := by
    intro j Ψ g
    rw [hT j Ψ g, hecke_eq c K (hw j) (hFK' j) (hsup j) (Ψ : H → V) ((mem _).1 Ψ.2).2, hr2]
    refine finsum_congr fun q => ?_
    rw [mul_assoc g (ζ (z j)), hw j]
  have hpres : ∀ j, ∀ Φ ∈ forms ι K ξ, rop (r j) Φ ∈ forms ι K ξ := by
    intro j Φ hΦ
    have e : ∀ g, rop (r j) Φ g = (T j ⟨Φ, hΦ⟩ : H → V) (g * (ζ (z j))⁻¹) := by
      intro g
      rw [hT']
      simp
    have hf := (mem _).1 (T j ⟨Φ, hΦ⟩).2
    refine (mem _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · rw [e, e, mul_assoc]
      exact hf.1 γ _
    · have hc : (ζ (z j))⁻¹ * k = k * (ζ (z j))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hw j k, mul_inv_cancel_right]
      rw [e, e, mul_assoc, ← hc, ← mul_assoc]
      exact hf.2 k hk _
  obtain ⟨Φ, hΦ, hne', hev, ψ, hψ⟩ := hE Γ H A Z V ι K ξ c ζ hζ φ hφ hne J r θ hr1 hpres
    (fun j u hu => by rw [hr2]; exact hθ j u hu)
  refine ⟨⟨Φ, hΦ⟩, fun h => hne' (congrArg Subtype.val h), ψ, hψ, fun j => ?_⟩
  apply Subtype.ext
  funext g
  rw [hT', hev j]
  show θ j • Φ (g * ζ (z j)) = (θ j * (ψ (z j) : ℂ)) • Φ g
  rw [hψ.1, mul_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace
section
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pProjTrace_holds :
    UpperTheory.Gal.CertificateRingHomMap.ProjTrace.{u} := by
  intro F _ W _ _ _ U p u hp h
  set q : W →ₗ[F] U := LinearMap.codRestrict U p hp.map_mem with hq
  have h1 : u * p = U.subtype ∘ₗ ((LinearMap.restrict u h) ∘ₗ q) := by
    ext x
    simp [q, LinearMap.restrict_apply]
  have h2 : q ∘ₗ U.subtype = LinearMap.id := by
    ext x
    simp [q, hp.map_id x x.2]
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]
end

