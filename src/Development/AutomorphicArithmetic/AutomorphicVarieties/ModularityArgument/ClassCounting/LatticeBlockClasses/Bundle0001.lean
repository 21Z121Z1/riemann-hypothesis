import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrismMul

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaVal
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem map_finset_prod_eq_sum_of_add_hom_on_subgroup {F M ι : Type} [Field F] [AddCommMonoid M] (U : Subgroup Fˣ)
    (f : Fˣ → M) (hf : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x + f y) (hf1 : f 1 = 0)
    (s : Finset ι) (g : ι → Fˣ) (hg : ∀ i ∈ s, g i ∈ U) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf1]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, g i ∈ U := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      hf _ (hg a (Finset.mem_insert_self a s)) _ (Subgroup.prod_mem U hs), ih hs]

private theorem sum_eq_sum_range_pow_of_cyclic_generator {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (γ : G)
    (hγ : ∀ σ : G, σ ∈ Subgroup.zpowers γ) (g : G → M) :
    ∑ σ, g σ = ∑ j ∈ Finset.range (orderOf γ), g (γ ^ j) := by
  classical
  have hfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  symm
  refine Finset.sum_nbij (fun j => γ ^ j) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro σ _
    have h := hfin.mem_powers_iff_mem_zpowers.mpr (hγ σ)
    rw [hfin.mem_powers_iff_mem_range_orderOf] at h
    simpa using h

theorem UpperTheory.V.ZK.Cl.cBetaVal :
    UpperTheory.V.ZK.Cl.CBetaVal := by
  intro L F _ _ _ _ _ l c ν E _ ζ γ hL kap hk U f hU hf α hα p
  set z := toF ζ with hzdef
  have hz : IsPrimitiveRoot z (l ^ ν) :=
    hL.prim.map_of_injective (Units.map_injective RingOfIntegers.coe_injective)
  have hcong : ∀ m n : ℕ, z ^ m = z ^ n → (m : ZMod (l ^ ν)) = n := fun m n h =>
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by rw [hz.eq_orderOf]; exact pow_eq_pow_iff_modEq.mp h)
  have hact : ∀ (σ τ : Gal(F/L)) (x : Fˣ), actU (σ * τ) x = actU σ (actU τ x) :=
    fun σ τ x => Units.ext rfl
  have hkm : ∀ σ τ : Gal(F/L), ((kap (σ * τ) : ℕ) : ZMod (l ^ ν)) = kap σ * kap τ := by
    intro σ τ
    rw [← Nat.cast_mul]
    apply hcong
    rw [← hk, hact, hk, map_pow, hk, ← pow_mul]
  have hkγ : ((kap γ : ℕ) : ZMod (l ^ ν)) = 1 + (l : ZMod (l ^ ν)) ^ c := by
    have h := hcong (kap γ) (1 + l ^ c) (by
      rw [← hk]
      ext
      simpa [actU, toF, z] using hL.act)
    simpa using h
  have hk1 : ((kap 1 : ℕ) : ZMod (l ^ ν)) = 1 := by
    have h := hcong (kap 1) 1 (by rw [← hk, pow_one]; exact Units.ext rfl)
    simpa using h
  have hkpow : ∀ j : ℕ, ((kap (γ ^ j) : ℕ) : ZMod (l ^ ν)) = (1 + (l : ZMod (l ^ ν)) ^ c) ^ j := by
    intro j
    induction j with
    | zero => simpa using hk1
    | succ j ih => rw [pow_succ, hkm, ih, hkγ, pow_succ]
  have hf1 : f 1 = 0 := by
    have h := hf 1 U.one_mem 1 U.one_mem
    rw [mul_one] at h
    simpa using h
  have hfn : ∀ x ∈ U, ∀ n : ℕ, f (x ^ n) = n * f x := by
    intro x hx n
    induction n with
    | zero => simp [hf1]
    | succ n ih =>
      rw [pow_succ, hf _ (U.pow_mem hx n) _ hx, ih]
      push_cast
      ring
  have hfz : ∀ x ∈ U, ∀ n : ℤ, f (x ^ n) = n * f x := by
    intro x hx n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, hfn x hx]
      push_cast
      ring
    · have h := hf _ (U.pow_mem hx m) _ (U.inv_mem (U.pow_mem hx m))
      rw [mul_inv_cancel, hf1, hfn x hx] at h
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -h
  have hUa : ∀ σ : Gal(F/L), actU σ α ∈ U := fun σ => hU σ α hα
  have hL1 : ∀ σ : Gal(F/L), f (actU σ (polAct γ p α)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * f (actU (σ * (γ ^ i)⁻¹) α) := by
    intro σ
    simp only [polAct, map_prod, map_zpow]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun i _ => U.zpow_mem (hU σ _ (hUa _)) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfz _ (hU σ _ (hUa _)), ← hact, inv_pow]
  set S := ∑ τ : Gal(F/L), (kap τ : ZMod (l ^ ν)) ^ E * f (actU τ α) with hSdef
  have hS : ∀ i : ℕ, ∑ σ : Gal(F/L), (kap σ : ZMod (l ^ ν)) ^ E * f (actU (σ * (γ ^ i)⁻¹) α) =
      ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i * S := by
    intro i
    rw [← (Equiv.mulRight (γ ^ i)).sum_comp, hSdef, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
      rw [hkm, hkpow]
      ring
    · intro _ _
      simp
  have hR : f (nrm γ ((1 + l ^ c) ^ E) α) = S := by
    simp only [nrm]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun j _ => U.pow_mem (hUa _) _), hSdef,
      sum_eq_sum_range_pow_of_cyclic_generator γ hL.gen]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfn _ (hUa _), hkpow]
    push_cast
    ring
  have hE : ((eval (((1 + l ^ c) ^ E : ℕ) : ℤ) p : ℤ) : ZMod (l ^ ν)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i := by
    rw [eval_eq_sum_range]
    push_cast
    rfl
  rw [hE, hR, Finset.sum_mul]
  simp_rw [hL1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← hS i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockVal
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

noncomputable section

namespace UpperTheory.V.ZK.Cl.BlockValuationRep

private theorem cyc_cm {A : Type} [CommRing A] {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Ch A G (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  rw [Cyc, (sChain A).2.1, show bd A G m z = 0 from hz, map_zero]

private def piRep {k : Type} [Field k] {G : Type} [Group G] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (ρ : ∀ b, G →* (U b ≃ₗ[k] U b)) : G →* ((∀ b, U b) ≃ₗ[k] ∀ b, U b) where
  toFun g := LinearEquiv.piCongrRight fun b => ρ b g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private def blk {k : Type} [Field k] {C : Type} [Group C] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (χ : B → C →* kˣ) (b : B) : (C × ∀ b, U b ≃ₗ[k] U b) →* (U b ≃ₗ[k] U b) where
  toFun p := scal (U b) (χ b p.1) * p.2 b
  map_one' := by simp
  map_mul' p p' := by
    ext w
    simp [scal, Units.smul_def, smul_smul, mul_comm]

private theorem pi_add {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} (hθ : IsAdd θ)
    {G : Type} [Group G] {z : Ch A G (m + 1)} (hz : Cyc z) (B : Type) [Fintype B] :
    ∀ (U : B → Type) [∀ b, AddCommGroup (U b)] [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z) := by
  refine Fintype.induction_empty_option (P := fun B _ => ∀ (U : B → Type) [∀ b, AddCommGroup (U b)]
      [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z)) ?_ ?_ ?_ B
  · intro α β _ e ih U _ _ _ V _ _ _ φ ρ ρ' h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← e.sum_comp]
    exact ih (fun a => U (e a)) V (φ.trans (LinearEquiv.piCongrLeft k U e).symm) ρ (fun a => ρ' (e a))
      fun g w a => h g w (e a)
  · intro U _ _ _ V _ _ _ φ ρ ρ' h
    haveI : Subsingleton V := φ.toEquiv.subsingleton
    haveI : Subsingleton (V ≃ₗ[k] V) := ⟨fun a b => LinearEquiv.ext fun _ => Subsingleton.elim _ _⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact hθ.bdry V _ ((sChain A).2.2.2.2 _ m _ (cyc_cm ρ hz))
  · intro α _ ih U _ _ _ V _ _ _ φ ρ ρ' h
    let ψ : V ≃ₗ[k] (U none × ∀ a, U (some a)) := φ.trans (LinearEquiv.piOptionEquivProd k)
    have hψ : (cj ψ).comp ρ = sumRep (ρ' none) (piRep (fun a => U (some a)) fun a => ρ' (some a)) := by
      refine MonoidHom.ext fun g => LinearEquiv.ext fun y => ?_
      obtain ⟨w, rfl⟩ := ψ.surjective y
      change ψ (ρ g (ψ.symm (ψ w))) = _
      rw [ψ.symm_apply_apply]
      exact Prod.ext (h g w none) (funext fun a => h g w (some a))
    rw [Fintype.sum_option, ← hθ.iso V _ ψ _ (cyc_cm ρ hz), ← (sChain A).2.2.1, hψ, hθ.add _ _ _ _ _ _ hz,
      ih (fun a => U (some a)) _ (LinearEquiv.refl k _) _ (fun a => ρ' (some a)) fun _ _ _ => rfl]

end UpperTheory.V.ZK.Cl.BlockValuationRep

open UpperTheory.V.ZK.Cl.BlockValuationRep in
theorem UpperTheory.V.ZK.Cl.cBlockVal :
    UpperTheory.V.ZK.Cl.CBlockVal := by
  unfold UpperTheory.V.ZK.Cl.CBlockVal
  intro k _ q _ e ζ hζ v θ hθ hv B _ U _ _ _ V _ _ _ φ σ g x g' hσ hg
  obtain ⟨-, -, h2, h3, -⟩ := sChain (ZMod q)
  let χ : B → Cq q →* kˣ := fun b => chi q ζ hζ (x b)
  let R : (Cq q × ∀ b, U b ≃ₗ[k] U b) →* (V ≃ₗ[k] V) := (cj φ.symm).comp (piRep U (blk U χ))
  have hR : ∀ p w b, φ (R p w) b = blk U χ b p (φ w b) := by
    intro p w b
    simp [R, cj, piRep]
  have hRg : R (1, g') = g := by
    refine LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hR, hg]
    simp [blk]
  have hRσ : R.comp (MonoidHom.inl _ _) = σ := by
    refine MonoidHom.ext fun c => LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hσ, MonoidHom.comp_apply, MonoidHom.inl_apply, hR]
    simp [blk, scal, Units.smul_def, χ]
  have hblk : ∀ b, (blk U χ b).comp (MonoidHom.inl _ _) = (scal (U b)).comp (χ b) := by
    intro b
    refine MonoidHom.ext fun c => ?_
    simp [blk]
  have hk0 : ∀ b, blk U χ b (1, g') = g' b := by
    intro b
    simp [blk]
  have hy : Cyc (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) :=
    cyc_cm _ (sZc q e)
  have hconj : (MulAut.conj ((1 : Cq q), g')⁻¹).toMonoidHom.comp (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) =
      MonoidHom.inl _ _ := by
    refine MonoidHom.ext fun c => ?_
    simp
  have hZ : Cyc (prism (ZMod q) ((1 : Cq q), g') (2 * e + 1 + 1)
      (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))) := by
    show bd _ _ (2 * e + 1 + 1) _ = 0
    have s := sPrism (ZMod q) _ ((1 : Cq q), g') (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))
    have hy' : bd (ZMod q) _ (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) = 0 := hy
    rw [hy', map_zero, add_zero, ← h2, hconj, sub_self] at s
    exact s
  show θ V (prism (ZMod q) g (2 * e + 1 + 1) (cm (ZMod q) σ (2 * e + 1 + 1) (zc q e))) = _
  rw [← hRg, ← hRσ, h2, ← h3]
  refine (pi_add hθ hZ B U V φ R (blk U χ) hR).trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [h3, ← h2, hblk b, hk0 b]
  exact hv (U b) (x b) (g' b)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CChain
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cChain :
    UpperTheory.V.ZK.Cl.CChain := by
  unfold UpperTheory.V.ZK.Cl.CChain
  intro A _ C D G _ _ _ ι _ m H ρ d n z g t₀ hz hB hc hρ hσ hg
  obtain ⟨-, h1, h2, h3, -⟩ := sChain A
  have hz' : bd A C m z = 0 := hz
  have hcyc : ∀ (K : Type) [Group K] (f : C →* K), bd A K m (cm A f (m + 1) z) = 0 := by
    intro K _ f
    rw [h1, hz', map_zero]
  let ρH : D →* H := ρ.codRestrict H hρ
  have hσ' : ∀ x, (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ x ∈ H := by
    intro x
    simpa using hσ x
  let σH : D →* H := ((MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ).codRestrict H hσ'
  let k : ι → H := fun t => (⟨(g t)⁻¹ * g t₀, hg t⟩ : H)⁻¹
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hB
  have hconj : ∀ t, (MulAut.conj (k t)⁻¹).toMonoidHom.comp (σH.comp (d t)) = ρH.comp (d t) := by
    intro t
    ext c
    have e := (hc t c).eq
    simp [σH, ρH, k]
    calc _ = (g t)⁻¹ * (ρ (d t c) * g t) := by group
      _ = ρ (d t c) := by rw [← e]; group
  refine ⟨cm A σH (m + 2) b - cm A ρH (m + 2) b + ∑ t, n t • prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z), ?_, ?_⟩
  · show bd A H (m + 1) _ = 0
    have hp : ∀ t, bd A H (m + 1) (prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z)) = cm A (ρH.comp (d t)) (m + 1) z - cm A (σH.comp (d t)) (m + 1) z := by
      intro t
      have e := sPrism A H (k t) m (cm A (σH.comp (d t)) (m + 1) z)
      rw [hcyc, map_zero, add_zero, ← h2] at e
      rw [e, hconj t]
    rw [map_add, map_sub, map_sum, h1, h1, hb]
    simp only [map_smul, hp, map_sum, ← h2, smul_sub, Finset.sum_sub_distrib]
    abel
  · have hk : ∀ t, H.subtype (k t) = (g t₀)⁻¹ * g t := by
      intro t
      simp [k]
    have hincl1 : H.subtype.comp σH = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ := by
      ext x
      rfl
    have hincl2 : H.subtype.comp ρH = ρ := by
      ext x
      rfl
    have hincl3 : ∀ t, H.subtype.comp (σH.comp (d t)) = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp (ρ.comp (d t)) := by
      intro t
      ext x
      rfl
    have hx : ∀ t, Cyc (cm A (ρ.comp (d t)) (m + 1) z) := fun t => hcyc G _
    choose e he using fun t => LinearMap.mem_range.mp (sPrismMul A G (g t₀) ((g t₀)⁻¹ * g t) m _ (hx t))
    have hS := sPrism A G (g t₀) (m + 1) (cm A ρ (m + 2) b)
    rw [h1, hb, ← h2] at hS
    refine LinearMap.mem_range.mpr ⟨prism A (g t₀) (m + 2) (cm A ρ (m + 2) b) - ∑ t, n t • e t, ?_⟩
    rw [map_sub, map_sum, eq_sub_of_add_eq hS]
    simp only [map_smul, he, mul_inv_cancel_left]
    simp only [map_add, map_sub, map_sum, map_smul, h3, hk, ← h2, hincl1, hincl2, hincl3]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CJoin
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cJoin : CJoin := by
  intro hChain hFree hTriv hAct hSplit hSupp hLatLoc hMu hInt hVal hGtNe hGtEq hBetaDiv
    hBetaVal hRep hUnit
  intro sChain sPrism sPrismMul sZc sRel sEta sStein
  intro L F _ _ _ _ _ l c ν e _ ζ γ hL he α 𝔡 hD
  classical
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hζq : ζ ^ (l ^ ν) = 1 := hL.prim.pow_eq_one
  have hR := hRep L F (l ^ ν) ζ hζq
  obtain ⟨kap, hkap⟩ := hR.2.2.2.2 hL.prim
  obtain ⟨b₀, hb₀, hsplit⟩ := hSplit L F hL.gal
  obtain ⟨b, hb, hb₀b, hbP⟩ := hSupp L F 𝔡 b₀ hb₀
  obtain ⟨n, t₀, hn, hrel⟩ := sRel l ν e
  obtain ⟨η, hη_ne, hη_eq⟩ := sEta l c ν (2 * e + 3) he hL.c_le t₀
  have hβ := hBetaDiv L F γ (1 + l ^ c) (2 * e + 3) (e + 1) (by omega) α 𝔡 hD
  set β := polAct γ (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) α with hβdef
  have hcar : ∀ t : Fin (2 * e + 4), ∃ g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν)),
      Carries L (l ^ ν) ζ (fun x => x.1 + ((t : ℕ) : ZMod (l ^ ν)) * x.2) (fun j => η j • 𝔡)
        (if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) g := by
    intro t
    by_cases ht : t = t₀
    · subst ht
      rw [if_pos rfl]
      refine hGtEq sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) l c ν (2 * e + 3) ζ γ hL _ η 𝔡
        (fun i => (pol ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3)).coeff i) β ⟨(1, 0), by simp⟩ ?_ hβ
      rw [hη_eq]
      simp [pol]
    · rw [if_neg ht]
      exact hGtNe sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) ζ _ η 𝔡 (hη_ne t ht)
  choose gG hgG using hcar
  have hmem : ∀ t, gG t ∈ GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b := by
    intro t
    refine hLatLoc L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b hb 0 (fun j => η j • 𝔡) ?_ ?_ (gG t) (hgG t).1
    · intro j P h
      simp at h
    · intro j P h
      apply hbP P
      intro h0
      apply h
      simp [h0]
  set Gr := GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b with hGr
  set Hs := (StabP L (InLat (0 : ZMod (l ^ ν) × ZMod (l ^ ν) → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf Gr with hHs
  let gs : Fin (2 * e + 4) → Gr := fun t => ⟨gG t, hmem t⟩
  let ρD : Cq (l ^ ν) × Cq (l ^ ν) →* Gr := (repD L (l ^ ν) ζ hζq).codRestrict Gr (fun x => hR.2.2.1 b x)
  have memStab : ∀ (p : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      g ∈ StabP L p ↔ ∀ x, p x ↔ p (g x) := fun _ _ => Iff.rfl
  have hstab : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g h : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p' x ↔ p' (h x)) → g⁻¹ * h * g ∈ StabP L p := by
    intro p p' g h hg hh
    rw [memStab]
    intro x
    rw [hg x, hg ((g⁻¹ * h * g) x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact hh (g x)
  have hstab2 : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g g' : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p x ↔ p' (g' x)) → g⁻¹ * g' ∈ StabP L p := by
    intro p p' g g' hg hg'
    rw [memStab]
    intro x
    rw [hg' x, hg ((g⁻¹ * g') x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hcomm : ∀ (t : Fin (2 * e + 4)) (c' : Cq (l ^ ν)), Commute (gs t) (ρD (dt (l ^ ν) (t : ℕ) c')) := by
    intro t c'
    have hc := hR.2.2.2.1 _ _ _ _ _ (hgG t) c'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, gs, ρD, MonoidHom.codRestrict_apply]
    rw [hR.1]
    exact hc.eq
  have hrhoH : ∀ x, ρD x ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    exact hR.2.1 0 x
  have hconj : ∀ x, (gs t₀)⁻¹ * ρD x * gs t₀ ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs, ρD, MonoidHom.codRestrict_apply]
    exact hstab _ _ _ _ (hgG t₀).1 ((memStab _ _).mp (hR.2.1 (fun j => η j • 𝔡) x))
  have hquot : ∀ t, (gs t)⁻¹ * gs t₀ ∈ Hs := by
    intro t
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs]
    exact hstab2 _ _ _ _ (hgG t).1 (hgG t₀).1
  obtain ⟨y, hyc, hyb⟩ := hChain (ZMod (l ^ ν)) (Cq (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) Gr
    (Fin (2 * e + 4)) (2 * e + 1) Hs ρD (fun t => dt (l ^ ν) (t : ℕ)) n (zc (l ^ ν) e) gs t₀
    (sZc (l ^ ν) e) hrel hcomm hrhoH hconj hquot
  obtain ⟨hfin, hproj, αI, hαI⟩ := hInt L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b
  haveI := hfin
  haveI := hproj
  obtain ⟨N, lam, hlam⟩ := hFree (𝓞 L) (ZMod (l ^ ν) × ZMod (l ^ ν) → 𝓞 F) Hs αI
  set w : ZMod (l ^ ν) := ((hn.unit⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) with hw
  set y' := w • y with hy'
  have hy'c : Cyc y' := by
    unfold Cyc at hyc ⊢
    rw [hy', map_smul, hyc, smul_zero]
  refine ⟨N, cm (ZMod (l ^ ν)) lam (2 * e + 1 + 1 + 1) y', algebraMap (𝓞 L) (𝓞 F) b, ?_, ?_, ?_⟩
  · unfold Cyc at hy'c ⊢
    rw [(sChain (ZMod (l ^ ν))).2.1]
    erw [hy'c, map_zero]
  · intro h
    apply hb
    exact FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 F) (by rw [h, map_zero])
  intro k _ _ r hr hrb hζ v θ hθ hv
  have hrb₀ : r (algebraMap (𝓞 L) (𝓞 F) b₀) ≠ 0 := by
    obtain ⟨c', hc'⟩ := hb₀b
    intro h0
    apply hrb
    rw [hc', map_mul, map_mul, h0, zero_mul]
  have hSp : Split L r := hsplit k r hr hrb₀
  obtain ⟨μ, hμ⟩ := hMu L F (ZMod (l ^ ν) × ZMod (l ^ ν)) k r b hrb hr hSp
  obtain ⟨U, f, hUdef, hUact, hfadd, hf1, hfres, hUres⟩ := hUnit L F k r b hrb (l ^ ν) v
  have hαU : α ∈ U := by
    rw [hUdef]
    intro P hP
    have h1 : 𝔡 P = 0 := by
      by_contra h0
      exact hP (hbP P h0)
    have h2 : 𝔡 (actP γ P) = 0 := by
      by_contra h0
      exact hP (((hAct L F).2.2.2.1 γ P b).mp (hbP _ h0))
    rw [hD P, h1, h2]
    simp
  have hnrmU : nrm γ ((1 + l ^ c) ^ (e + 1)) α ∈ U := by
    unfold nrm
    exact Subgroup.prod_mem U fun j _ => U.pow_mem (hUact _ _ hαU) _
  obtain ⟨u, hu⟩ := hUres _ hnrmU
  refine ⟨u, hu, ?_⟩
  rw [← hfres _ _ hu]
  obtain ⟨π, hπ1, hπ2, hπ3, hπ4⟩ := hαI k r hSp μ hμ
  obtain ⟨P, φ, hφ⟩ := hlam k (r.comp (algebraMap (𝓞 L) (𝓞 F))) hr
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) π (μ.comp Hs.subtype) hπ1 hπ2 hπ3 hπ4
  beta_reduce at hyb
  rw [← (sChain (ZMod (l ^ ν))).2.2.1, hφ]
  refine Eq.trans (hTriv k (ZMod (l ^ ν)) (2 * e + 1 + 1) θ hθ Hs
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) P (Fin N → k) (μ.comp Hs.subtype) φ y' hy'c) ?_
  rw [(sChain (ZMod (l ^ ν))).2.2.1]
  change θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
    (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) (w • y))) = _
  rw [map_smul, map_smul, map_smul]
  have hA : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) y)) =
      ∑ t : Fin (2 * e + 4), n t • θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
          (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) := by
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyb
    have h0 : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (bd _ _ _ x)) = 0 :=
      hθ.bdry _ _ (LinearMap.mem_range.mpr ⟨cm (ZMod (l ^ ν)) μ _ x, (sChain _).2.1 _ _ μ _ x⟩)
    rw [hx, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h0
    rw [h0]
    simp only [map_smul]
  have hT : ∀ t : Fin (2 * e + 4), θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
        (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) =
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) := by
    intro t
    erw [(sChain (ZMod (l ^ ν))).2.2.2.1, ← (sChain (ZMod (l ^ ν))).2.2.1]
    exact hVal L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) e ζ hζq kap hkap k r b hrb hSp μ hμ hζ v θ hθ hv
      f hfres _ _ _ (gs t) (ρD.comp (dt (l ^ ν) (t : ℕ))) (hgG t)
      (fun c' => by simp only [ρD, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]; exact hR.1 t c')
  have hT0 : ∀ t : Fin (2 * e + 4), t ≠ t₀ →
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) = 0 := by
    intro t ht
    simp [if_neg ht, hf1]
  have hTt₀ : ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t₀ = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) =
      ∑ σ, (kap σ : ZMod (l ^ ν)) ^ (e + 1) * f (actU σ β) := by
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_eq_single (1 : ZMod (l ^ ν))]
    · simp
    · intro x _ hx
      simp [hx, hf1]
    · simp
  have hBV := hBetaVal L F l c ν (e + 1) ζ γ hL kap hkap U f hUact hfadd α hαU
    (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1))
  have hev : ((eval (((1 + l ^ c) ^ (e + 1) : ℕ) : ℤ) (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) : ℤ) :
      ZMod (l ^ ν)) = ((pe (1 + l ^ c) (2 * e + 3) (e + 1) : ℤ) : ZMod (l ^ ν)) := by
    congr 1
    simp [polE, pe, eval_prod]
  rw [hA, Finset.sum_eq_single t₀ (fun t _ ht => by rw [hT t, hT0 t ht, smul_zero]) (by simp),
    hT t₀, hTt₀, hBV, hev, smul_eq_mul, smul_eq_mul, ← mul_assoc, hw, hn.val_inv_mul, one_mul]
end

