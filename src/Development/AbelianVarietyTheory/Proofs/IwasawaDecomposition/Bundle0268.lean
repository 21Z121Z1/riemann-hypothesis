import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCove
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  ext i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  rw [MvPolynomial.coeff_zero, hq]
  exact hg _ _ hk

theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetz
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem isCompl_strand_lowPart (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : ℤ → Submodule ℂ V) (N : Module.End ℂ V) (m : ℕ) (hi : iSupIndep U)
    (ht : ⨆ i, U i = ⊤) (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2))
    (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-(i : ℤ))) (U i))
    (hm : ∀ k : ℤ, (m : ℤ) < k → U k = ⊥) :
    IsCompl (strand N (U (-(m : ℤ))) m) (lowPart U N m) := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_proj_of_iSupIndep hi ht
  have hhigh : ∀ d : ℤ, (m : ℤ) < d → ∀ v ∈ U d, v = 0 := fun d hd v hv => by
    rw [hm d hd] at hv; exact (Submodule.mem_bot ℂ).mp hv
  have hlow : ∀ d : ℤ, d < -(m : ℤ) → ∀ v ∈ U d, v = 0 := by
    intro d hd v hv
    refine eq_zero_of_pow_eq_zero hb (m := (-d).toNat) (by omega) hv ?_
    exact hhigh (-d) (by omega) _ (pow_mem_of_degree_two hN (-d).toNat (by omega) hv)
  have fC : ∀ x ∈ lowPart U N m, ∀ d, (N ^ (((m : ℤ) - d + 1) / 2).toNat) (p d x) = 0 := by
    intro x hx d
    unfold lowPart at hx
    induction hx using Submodule.iSup_induction' with
    | mem k y hy =>
      by_cases hk : k = d
      · subst hk; rw [h2 k y hy.1]; exact hy.2
      · rw [h3 d k hk y hy.1, map_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  have fB : ∀ x ∈ strand N (U (-(m : ℤ))) m, ∀ d, ∃ u ∈ U (-(m : ℤ)),
      p d x = (N ^ ((d + m) / 2).toNat) u ∧ (d = -m + 2 * (((d + m) / 2).toNat : ℤ) ∨ u = 0) := by
    intro x hx d
    unfold strand at hx
    induction hx using Submodule.iSup_induction' with
    | mem j y hy =>
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
      have hjw := pow_mem_of_degree_two hN (j : ℕ) rfl hw
      by_cases hd : d = -(m : ℤ) + 2 * ((j : ℕ) : ℤ)
      · refine ⟨w, hw, ?_, Or.inl (by omega)⟩
        rw [h2 d _ (hd ▸ hjw)]
        have : ((d + m) / 2).toNat = (j : ℕ) := by omega
        rw [this]
      · refine ⟨0, zero_mem _, ?_, Or.inr rfl⟩
        rw [h3 d _ (fun h => hd h.symm) _ hjw, map_zero]
    | zero => exact ⟨0, zero_mem _, by simp, Or.inr rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨u1, hu1, e1, o1⟩ := hy
      obtain ⟨u2, hu2, e2, o2⟩ := hz
      refine ⟨u1 + u2, add_mem hu1 hu2, by rw [map_add, e1, e2, map_add], ?_⟩
      rcases o1 with o1 | o1
      · exact Or.inl o1
      · rcases o2 with o2 | o2
        · exact Or.inl o2
        · right; rw [o1, o2, add_zero]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hB hC
    refine h4 ⊥ x fun d => ?_
    rw [Submodule.mem_bot]
    by_cases hdm : (m : ℤ) < d
    · exact hhigh d hdm _ (h1 d x)
    obtain ⟨u, hu, e, o⟩ := fB x hB d
    rcases o with o | o
    · have h5 := fC x hC d
      rw [e, ← End.mul_apply, ← pow_add] at h5
      have hs : (((m : ℤ) - d + 1) / 2).toNat + ((d + m) / 2).toNat = m := by omega
      rw [hs] at h5
      rw [e, eq_zero_of_pow_eq_zero hb (d := -(m : ℤ)) (m := m) (by omega) hu h5, map_zero]
    · rw [e, o, map_zero]
  · rw [codisjoint_iff, eq_top_iff, ← ht]
    refine iSup_le fun d v hv => ?_
    by_cases hdm : (m : ℤ) < d
    · rw [hhigh d hdm v hv]; exact zero_mem _
    by_cases hdl : d < -(m : ℤ)
    · rw [hlow d hdl v hv]; exact zero_mem _
    set e := (((m : ℤ) - d + 1) / 2).toNat with he
    have hC : ∀ w ∈ U d, (N ^ e) w = 0 → w ∈ lowPart U N m := fun w hw h0 => by
      unfold lowPart
      exact Submodule.mem_iSup_of_mem d ⟨hw, h0⟩
    by_cases hpar : d + 2 * (e : ℤ) = m + 1
    · apply Submodule.mem_sup_right
      refine hC v hv (hhigh _ (by omega : (m : ℤ) < m + 1) _ ?_)
      exact pow_mem_of_degree_two hN e hpar.symm hv
    · have hw : (N ^ e) v ∈ U m := pow_mem_of_degree_two hN e (by omega) hv
      obtain ⟨u, hu, hu'⟩ := exists_pow_eq hN hb (m := m) (d := m) (e := -(m : ℤ)) le_rfl
        (by ring) hw
      set j := ((d + m) / 2).toNat with hjdef
      have hjm : j < m + 1 := by omega
      have hNj : (N ^ j) u ∈ strand N (U (-(m : ℤ))) m := by
        unfold strand
        exact Submodule.mem_iSup_of_mem (⟨j, hjm⟩ : Fin (m + 1)) ⟨u, hu, rfl⟩
      have hv' : v = (N ^ j) u + (v - (N ^ j) u) := by abel
      rw [hv']
      refine Submodule.add_mem_sup hNj (hC _ (sub_mem hv (pow_mem_of_degree_two hN j (by omega) hu)) ?_)
      rw [map_sub, ← End.mul_apply, ← pow_add, show e + j = m by omega, hu', sub_self]

end GlobalTheory.WeilDeligne.PrimDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.ProjPts

open GlobalTheory.ZH.RatModel GlobalTheory.Points

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
  {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}

theorem exists_open_span_le {J : Type} [Fintype J] (a b : J → J → Ω) {z : M.Z}
    (h : Submodule.span (M.O z) (Set.range a) ≤ Submodule.span (M.O z) (Set.range b)) :
    ∃ V : M.Z.Opens, z ∈ V ∧ ∀ w ∈ V, Submodule.span (M.O w) (Set.range a) ≤ Submodule.span (M.O w) (Set.range b) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨⟨⋂ i, ⋂ l, {w | (c i l : Ω) ∈ M.O w}, isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l =>
    M.isOpen_setOf_mem_O _⟩, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun l => (c i l).2, fun w hw => ?_⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2
    ⟨fun l => ⟨c i l, Set.mem_iInter.1 (Set.mem_iInter.1 hw i) l⟩, hc i⟩

theorem exists_affine_basis {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (B : Matrix J J Ω) {z : M.Z}
    (h : EE.E z = Submodule.span (M.O z) (Set.range B)) :
    ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ ∀ w ∈ W, EE.E w = Submodule.span (M.O w) (Set.range B) := by
  obtain ⟨U, b, hz, -, H⟩ := EE.loc z
  have e := (H z hz).symm.trans h
  obtain ⟨V₁, h₁, H₁⟩ := exists_open_span_le b B e.le
  obtain ⟨V₂, h₂, H₂⟩ := exists_open_span_le B b e.ge
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U ⊓ V₁ ⊓ V₂) (x := z) ⟨⟨hz, h₁⟩, h₂⟩
  exact ⟨W, hW, hzW, fun w hw => (H w (hle hw).1.1).trans (le_antisymm (H₁ w (hle hw).1.2) (H₂ w (hle hw).2))⟩

variable {K : Type} [Field K]

theorem range_subset {p : Sp K ⟶ M.Z} {U : M.Z.Opens} (h : p (IsLocalRing.closedPoint K) ∈ U) :
    Set.range p ⊆ U := by
  rw [range_eq_singleton p (IsLocalRing.closedPoint K), Set.singleton_subset_iff]
  exact h

theorem exists_point {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty)
    (ψ : M.ringOn U →+* K) :
    ∃ p : Sp K ⟶ M.Z, p (IsLocalRing.closedPoint K) ∈ U ∧ ∀ a : M.ringOn U, M.val p a = ψ a := by
  let χ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (ψ.comp (M.sectionsEquiv U hne).toRingHom)
  have h := le_preimage_specMap_fromSpec hU χ
  refine ⟨Spec.map χ ≫ hU.fromSpec, (le_preimage_iff _ _).1 h, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := (M.sectionsEquiv U hne).surjective a
  rw [coe_sectionsEquiv, val_valF ((top_le_preimage_iff _ _).1 h), valF_eq_valR, valR_eq _ _ h,
    valMap_specMap_fromSpec]
  rfl

theorem ext_of_val {U : M.Z.Opens} (hU : IsAffineOpen U) {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U)
    (H : ∀ a ∈ M.ringOn U, M.val p a = M.val q a) : p = q := by
  refine ext_of_valR hU ((le_preimage_iff _ _).2 hp) ((le_preimage_iff _ _).2 hq) fun g => ?_
  have := H _ ((mem_ringOn_iff_exists ⟨_, hp⟩).2 ⟨g, rfl⟩)
  rwa [val_valF (range_subset hp), val_valF (range_subset hq)] at this

theorem val_eq_of_adjoin {U : M.Z.Opens} {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U) {T : Set Ω}
    (hT : M.ringOn U = Algebra.adjoin F T) (h0 : ∀ a, M.val p (algebraMap F Ω a) = M.val q (algebraMap F Ω a))
    (h1 : ∀ a ∈ T, M.val p a = M.val q a) : ∀ a ∈ M.ringOn U, M.val p a = M.val q a := by
  have sp := specializes_of_range_eq (range_eq_singleton p (IsLocalRing.closedPoint K))
  have sq := specializes_of_range_eq (range_eq_singleton q (IsLocalRing.closedPoint K))
  intro a ha
  rw [hT] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h1 x hx
  | algebraMap r => exact h0 r
  | add x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_add sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_add sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]
  | mul x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_mul sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_mul sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]

theorem exists_ringHom (R : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) (S : Subalgebra F Ω')
    {T : Set Ω'} (hS : S = Algebra.adjoin F (φ '' (R : Set Ω) ∪ T)) (hT : ∀ y ∈ T, y = 1 ∨ y ∈ Set.range t)
    (v : R →+* K) (c : σ → K) :
    ∃ ψ : S →+* K, (∀ (r : R) (h : φ r ∈ S), ψ ⟨φ r, h⟩ = v r) ∧ ∀ j (h : t j ∈ S), ψ ⟨t j, h⟩ = c j := by
  let g : MvPolynomial σ R →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp R.val.toRingHom) t
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := ht (MvPolynomial.map R.val.toRingHom P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact MvPolynomial.map_injective R.val.toRingHom Subtype.val_injective (this.trans (map_zero _).symm)
  have hC : ∀ r : R, g (MvPolynomial.C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ r
  have hX : ∀ j, g (MvPolynomial.X j) = t j := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hle : ∀ y ∈ S, y ∈ g.range := by
    intro y hy
    rw [hS] at hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩ | hx
      · exact ⟨_, hC ⟨r, hr⟩⟩
      · rcases hT x hx with rfl | ⟨j, rfl⟩
        · exact one_mem _
        · exact ⟨_, hX j⟩
    | algebraMap r => exact ⟨_, (hC (algebraMap F R r)).trans (φ.commutes r)⟩
    | add x y _ _ ex ey => exact add_mem ex ey
    | mul x y _ _ ex ey => exact mul_mem ex ey
  let e : MvPolynomial σ R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  let ι : S →+* g.range := S.val.toRingHom.codRestrict g.range fun y => hle y y.2
  have key : ∀ (P : MvPolynomial σ R) (y : S), g P = y → e.symm (ι y) = P := fun P y h =>
    e.symm_apply_eq.2 (Subtype.ext h.symm)
  refine ⟨(MvPolynomial.eval₂Hom v c).comp (e.symm.toRingHom.comp ι), fun r h => ?_, fun j h => ?_⟩
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hC r))).trans (MvPolynomial.eval₂Hom_C _ _ r)
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hX j))).trans (MvPolynomial.eval₂Hom_X' _ _ j)

theorem div_of_ne_zero {J : Type} {t : J → Ω} {p : Sp K ⟶ M.Z} {c : J → K} {i k : J} (hi : c i ≠ 0)
    (hk : M.Div t k (p (IsLocalRing.closedPoint K))) (h : ∀ j, c j = c k * M.val p (t j / t k)) :
    M.Div t i (p (IsLocalRing.closedPoint K)) ∧ ∀ j, M.val p (t j / t i) = c j / c i := by
  have hr := range_eq_singleton p (IsLocalRing.closedPoint K)
  have h0 : M.val p (t i / t k) ≠ 0 := right_ne_zero_of_mul (h i ▸ hi)
  have hd : M.Div t i (p (IsLocalRing.closedPoint K)) :=
    (hk.div_iff_isUnit i).2 ((val_ne_zero_iff hr ⟨_, hk.2 i⟩).1 h0)
  refine ⟨hd, fun j => ?_⟩
  have e := val_mul (specializes_of_range_eq hr) (hd.2 j) (hk.2 i)
  rw [div_mul_div_cancel₀ hd.1] at e
  rw [eq_div_iff hi, h j, h i, e]
  ring

theorem projPoints {J : Type} [Fintype J] [DecidableEq J] {EE : M.Lat J} {s : J → Ω'}
    (H : ProjBundle M EE M' φ f s) : ProjPoints M EE M' φ f s := by
  refine ⟨H.hom, fun z' B _ hB => ?_, fun K _ x B hB hE c hc => ?_⟩
  · obtain ⟨W, hW, hz, hE⟩ := exists_affine_basis EE B hB
    exact (H.chart W B hW ⟨_, hz⟩ hE).1 z' hz
  obtain ⟨W, hW, hz, hEW⟩ := exists_affine_basis EE B hE
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  replace hi : c i ≠ 0 := hi
  obtain ⟨hti, hind⟩ := H.gen B hB i
  obtain ⟨U, hU, hUeq, hR⟩ := (H.chart W B hW ⟨_, hz⟩ hEW).2 i hti
  set t := (B.map φ).mulVec s with ht
  have hmem : ∀ z', z' ∈ U ↔ f z' ∈ W ∧ M'.Div t i z' := fun z' => Set.ext_iff.1 hUeq z'
  have hne : (U : Set M'.Z).Nonempty := by
    refine ⟨genericPoint M'.Z, (hmem _).2 ⟨?_, div_genericPoint hti⟩⟩
    rw [← M'.pt_apply (IsLocalRing.closedPoint Ω')]
    have e : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ∈ W := by
      rw [H.hom]
      exact M.top_le_preimage_pt ⟨_, hz⟩ (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    exact e
  let v : M.ringOn W →+* K := (valHom x _ (range_eq_singleton x (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (ringOn_le_O hz)).toRingHom
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_ringHom (M.ringOn W) _ hind (M'.ringOn U) hR (by
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · exact Or.inl (by rw [hj]; exact div_self hti)
    · exact Or.inr ⟨⟨j, hj⟩, rfl⟩) v fun j => c j.1 / c i
  obtain ⟨p, hp, hv⟩ := exists_point hU hne ψ
  have hφ : ∀ a ∈ M.ringOn W, φ a ∈ M'.ringOn U := fun a ha =>
    hR ▸ Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩)
  have hcomp : ∀ q : Sp K ⟶ M'.Z, q (IsLocalRing.closedPoint K) ∈ U → ∀ a ∈ M.ringOn W,
      M.val (q ≫ f) a = M'.val q (φ a) := fun q hq a ha =>
    H.hom.val_comp q _ (ringOn_le_O ((hmem _).1 hq).1 ha)
  have hpf : p ≫ f = x := by
    refine ext_of_val hW ((hmem _).1 hp).1 hz fun a ha => ?_
    exact (hcomp p hp a ha).trans ((hv ⟨_, hφ a ha⟩).trans (hψ₁ ⟨a, ha⟩ _))
  have hrat : ∀ j, M'.val p (t j / t i) = c j / c i := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hti, div_self hi, RatModel.val_one]
    · have hm : t j / t i ∈ M'.ringOn U := hR ▸ Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      exact (hv ⟨_, hm⟩).trans (hψ₂ ⟨j, hj⟩ hm)
  refine ⟨p, ⟨hpf, i, ((hmem _).1 hp).2, fun j => by rw [hrat, mul_div_cancel₀ _ hi]⟩, ?_⟩
  rintro q ⟨hqf, k, hk, hq⟩
  obtain ⟨hd, hqr⟩ := div_of_ne_zero hi hk hq
  have hqU : q (IsLocalRing.closedPoint K) ∈ U := (hmem _).2 ⟨by rw [← hqf] at hz; exact hz, hd⟩
  have hb : ∀ a ∈ M.ringOn W, M'.val q (φ a) = M'.val p (φ a) := fun a ha => by
    rw [← hcomp q hqU a ha, ← hcomp p hp a ha, hqf, hpf]
  refine ext_of_val hU hqU hp (val_eq_of_adjoin hqU hp hR (fun a => ?_) ?_)
  · rw [← φ.commutes]
    exact hb _ (Subalgebra.algebraMap_mem _ a)
  · rintro _ (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
    · exact hb a ha
    · exact (hqr j).trans (hrat j).symm

end GlobalTheory.FlagBundle.ProjPts

theorem GlobalTheory.FlagBundle.projPoints_of_projBundle : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω']
    [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J]
    [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => GlobalTheory.FlagBundle.ProjPts.projPoints H

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices

set_option maxHeartbeats 1000000 in

theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
end

